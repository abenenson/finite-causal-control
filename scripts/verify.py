#!/usr/bin/env python3
"""Rebuild authored modules, re-elaborate full lint, and audit named transitive axioms."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import os
from datetime import datetime, timezone
from pathlib import Path

if not __debug__:
    raise SystemExit('Verification requires enabled Python assertions; omit -O/PYTHONOPTIMIZE.')


def uncomment(source):
    """Erase nested Lean comments and strings while preserving command line positions."""
    result, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                index += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                index += 2
            else:
                result.append('\n' if char == '\n' else ' ')
                index += 1
        elif quoted:
            if char == '\\':
                result.extend('  ')
                index += 2
            else:
                quoted = char != '"'
                result.append('\n' if char == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            result.extend('  ')
            index += 2
        elif pair == '--':
            end = source.find('\n', index)
            end = len(source) if end < 0 else end
            result.extend(' ' * (end - index))
            index = end
        elif char == '"':
            quoted = True
            result.append(' ')
            index += 1
        else:
            result.append(char)
            index += 1
    assert not depth and not quoted, 'Unterminated comment or string'
    return ''.join(result)


def declarations(source):
    """Enumerate explicit public names; anonymous and generated declarations are separate."""
    stack, names = [], []
    for line in uncomment(source).splitlines():
        if line != line.lstrip():
            continue
        line = re.sub(r'^@\[[^\]]*\]\s*', '', line)
        match = re.match(r'namespace\s+([\w.]+)', line)
        if match:
            stack.append(('namespace', match[1]))
            continue
        if re.match(r'(?:noncomputable\s+)?section\b', line):
            stack.append(('section', ''))
            continue
        if re.match(r'end(?:\s|$)', line):
            assert stack, line
            stack.pop()
            continue
        match = re.match(
            r'((?:(?:private|protected|noncomputable|unsafe)\s+)*)'
            r'(?:theorem|lemma|def|abbrev|structure|class|instance)\s+([\w.]+)', line)
        if match and 'private' not in match[1].split():
            prefix = [name for kind, name in stack if kind == 'namespace']
            names.append('.'.join(prefix + [match[2]]))
    assert not stack, stack
    return names



def check_diagnostics(output, *, json_mode=False):
    """Fail closed on native/JSON diagnostics, including erroneous zero-exit output."""
    def check_text(text):
        assert 'PANIC' not in text and not re.search(r'(?im)\bpanic:', text), 'Native panic'
        assert not re.search(r'(^|: )(?:warning|error):', text, re.M), text

    check_text(output)
    for raw in output.splitlines():
        line = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', raw).strip()
        if not line:
            continue
        check_text(line)
        if not json_mode and not line.startswith('{'):
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError as error:
            raise AssertionError('Malformed diagnostic JSON: ' + line) from error
        assert isinstance(message, dict), 'Unknown diagnostic JSON'
        assert message.get('severity') in {'information', 'warning', 'error'}, message
        assert isinstance(message.get('data'), str), message
        assert message['severity'] == 'information', message
        check_text(message['data'])


def imported_modules(source):
    """Read every ordinary import; unsupported header syntax fails closed."""
    tokens = re.findall(r"[A-Za-z_][\w.']*|[^\s]", uncomment(source))
    boundary = {'import', 'prelude', 'module', 'public', 'private', 'meta', 'open',
                'namespace', 'section', 'noncomputable', 'universe', 'universes',
                'variable', 'variables', 'export', 'attribute', 'set_option',
                'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class',
                'end', 'example', 'axiom', 'constant', 'opaque', 'inductive',
                'syntax', 'macro', 'elab', 'initialize', '#', '@'}
    modules = []
    for index, token in enumerate(tokens):
        if token != 'import':
            continue
        index += 1
        if index < len(tokens) and tokens[index] == 'all':
            index += 1
        start = len(modules)
        while index < len(tokens) and tokens[index] not in boundary:
            name = tokens[index]
            assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                                name), 'Unsupported import header: ' + name
            modules.append(name)
            index += 1
        assert len(modules) > start, 'Empty or unsupported import header'
    return modules


def clear_authored_artifacts(root, source_files):
    """Force authored recompilation without deleting or traversing dependency caches."""
    library = root / '.lake' / 'build' / 'lib' / 'lean'
    suffixes = ('.olean', '.ilean', '.ir', '.trace')
    removed = []
    for relative in source_files:
        source = Path(relative)
        assert not source.is_absolute() and '..' not in source.parts
        assert source.suffix == '.lean', relative
        module = library / source.with_suffix('')
        current = root
        for part in module.parent.relative_to(root).parts:
            current = current / part
            assert not current.is_symlink(), 'Linked authored artifact directory: ' + str(current)
            assert not current.exists() or current.is_dir(), str(current)
        if not module.parent.is_dir():
            continue
        for artifact in sorted(module.parent.iterdir()):
            if not any(artifact.name == module.name + suffix or
                       artifact.name.startswith(module.name + suffix + '.')
                       for suffix in suffixes):
                continue
            assert artifact.is_file() or artifact.is_symlink(), str(artifact)
            artifact.unlink()
            removed.append(str(artifact.relative_to(root)))
    return removed


def manifest_dependencies(packages):
    """Read supported single-component Lake names without changing package paths or pins."""
    dependencies = {}
    for entry in packages:
        serialized = entry['name']
        assert isinstance(serialized, str), 'Non-string manifest package name'
        name = (serialized[1:-1] if serialized.startswith('«') and serialized.endswith('»')
                else serialized)
        assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*', name), \
            'Unsupported manifest package name: ' + serialized
        assert name not in dependencies, 'Duplicate manifest package name: ' + name
        dependencies[name] = entry
    return dependencies


def import_roots(config):
    """Allow extra library roots only for explicitly pinned public dependencies."""
    roots = [config['root_module'], config['examples_module']]
    modules = config.get('dependency_modules', {})
    assert isinstance(modules, dict), 'dependency_modules must map dependency names to roots'
    for name, additions in modules.items():
        assert name in config['public_dependencies'], 'Unpinned dependency module: ' + name
        pin = config['public_dependencies'][name]
        assert re.fullmatch(r'[0-9a-f]{40}', pin.get('rev', '')), name
        assert re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',
                            pin.get('url', '')), name
        assert isinstance(additions, list) and additions, name
        roots.extend(additions)
    for name in roots:
        assert isinstance(name, str) and re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name), name
        assert name != 'Mathlib', 'Use focused Mathlib imports'
    return roots


def allowed_import(module, roots):
    """Recognize focused Mathlib imports and the declared library module roots."""
    return module.startswith('Mathlib.') or any(
        module == root or module.startswith(root + '.') for root in roots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-dir', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    config = json.loads((root / 'verification.json').read_text())
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    evidence = args.evidence_dir or root / 'verification-artifacts' / stamp
    evidence = evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    record = {'status': 'running', 'stages': [], 'source_sha256': {},
              'axioms': {}, 'scope': 'Authored sources and explicit named transitive dependencies'}

    def save():
        (evidence / 'qualification.json').write_text(json.dumps(record, indent=2) + '\n')

    def run(name, command, stdin=None):
        result = subprocess.run(command, cwd=root, input=stdin, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (evidence / (name + '.log')).write_text(result.stdout)
        record['stages'].append({'name': name, 'command': command,
                                 'exit_code': result.returncode})
        save()
        print(name, result.returncode, flush=True)
        assert result.returncode == 0, name
        check_diagnostics(result.stdout)
        return result.stdout

    def messages(output):
        check_diagnostics(output, json_mode=True)
        data = []
        for line in output.splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                data.append(line)
                continue
            assert message.get('severity') not in {'warning', 'error'}, message
            data.append(message.get('data', ''))
        joined = '\n'.join(data)
        assert not re.search(r'(^|: )(?:warning|error):', joined, re.M), joined
        return joined

    try:
        actual_sources = {str(p.relative_to(root)) for p in root.rglob('*.lean')
                          if not {'.lake', '.git', 'verification-artifacts'} &
                          set(p.relative_to(root).parts)}
        assert actual_sources == set(config['source_files']) | {'lakefile.lean'}, \
            'Authored Lean file coverage differs from manifest'
        toolchain = (root / 'lean-toolchain').read_text().strip()
        version = run('compiler-version', ['lake', 'env', 'lean', '--version']).strip()
        assert toolchain == 'leanprover/lean4:v4.35.0' and 'version 4.35.0,' in version
        record['compiler_version'] = version
        manifest = json.loads((root / 'lake-manifest.json').read_text())
        dependencies = manifest_dependencies(manifest['packages'])
        assert set(dependencies) == set(config['public_dependencies'])
        record['dependency_revisions'] = {}
        for name, expected in config['public_dependencies'].items():
            actual = dependencies[name]
            assert actual['type'] == 'git' and actual['rev'] == expected['rev']
            assert actual['url'] == expected['url']
            head = subprocess.check_output(
                ['git', '--no-optional-locks', '--no-replace-objects', '-C',
                 str(root / '.lake/packages' / name), 'rev-parse', 'HEAD'],
                text=True).strip()
            assert head == expected['rev'], name
            record['dependency_revisions'][name] = head
        roots = import_roots(config)
        names = []
        for relative in config['source_files']:
            path = root / relative
            source = path.read_text()
            code = uncomment(source)
            record['source_sha256'][relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            assert not re.search(r'\b(?:sorry|admit|sorryAx)\b', code), relative
            assert not re.search(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|unsafe|noncomputable)\s+)*(?:axiom|constant)\b', code, re.M), relative
            assert all(len(line) <= 100 for line in source.splitlines()), relative
            assert source.count('Copyright (c)') == 1 and '/-!' in source, relative
            for module in imported_modules(source):
                assert allowed_import(module, roots), (relative, module)
            names.extend(declarations(source))
        assert names and len(names) == len(set(names))
        assert names == config['declarations'], 'Declaration manifest differs from actual sources'
        record['removed_authored_artifacts'] = clear_authored_artifacts(
            root, config['source_files'])
        save()
        targets = ['+' + str(Path(p).with_suffix('')).replace('/', '.') + ':olean'
                   for p in config['source_files']]
        run('exact-build', ['lake', '--rehash', '--wfail', 'build', *targets])
        for relative in config['source_files']:
            path = evidence / 'lint-sources' / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            source = (root / relative).read_text()
            assert re.search(r'^module$', source, re.M), relative
            source = source.replace('module\n',
                                    'module\nimport Mathlib.Tactic.Linter.Lint\n', 1)
            path.write_text(source + '\n#lint docBlame docBlameThm\n')
            output = run('lint-' + relative.replace('/', '-'),
                         ['lake', 'env', 'lean', '-j2', '--json',
                          '--root=' + str(evidence / 'lint-sources'), str(path)])
            clean = messages(output)
            assert '-- All linting checks passed!' in clean, relative
            assert 'with 16 linters' in clean, relative
        probe = 'module\n' + '\n'.join(
            'import ' + name for name in config['audit_imports']) + '\n'
        probe += '\n'.join('#print axioms ' + name for name in names) + '\n'
        (evidence / 'axioms.lean').write_text(probe)
        output = messages(run('axioms', ['lake', 'env', 'lean', '-j2', '--json',
                                        str(evidence / 'axioms.lean')]))
        pattern = r"'([\w.]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
        reports = re.findall(pattern, output)
        assert len(reports) == len(names) and {n for n, _ in reports} == set(names)
        for name, raw in reports:
            axioms = {x.strip() for x in raw.split(',') if x.strip()}
            assert axioms <= {'Classical.choice', 'Quot.sound', 'propext'}, (name, axioms)
            record['axioms'][name] = sorted(axioms)
        record.update(status='passed', full_linter_count=16, named_declaration_count=len(names))
        save()
        print('PASS:', len(config['source_files']), 'files;', len(names), 'named declarations')
    except Exception as error:
        record.update(status='failed', failure=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
