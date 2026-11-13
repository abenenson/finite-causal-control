"""Fetch only the Mathlib closure used by authored and pinned public library sources."""
import json
from pathlib import Path
import subprocess

import verify


def source_paths(root, config):
    """Include authored files and every declared public dependency module root."""
    paths = {root / relative for relative in config['source_files']}
    verify.import_roots(config)
    for package, modules in config.get('dependency_modules', {}).items():
        package_root = root / '.lake' / 'packages' / package
        for module in modules:
            relative = Path(*module.split('.'))
            entry = package_root / relative.with_suffix('.lean')
            directory = package_root / relative
            found = ([entry] if entry.is_file() else [])
            if directory.is_dir():
                found.extend(directory.rglob('*.lean'))
            assert found, 'Missing pinned dependency module root: ' + module
            paths.update(found)
    for path in paths:
        assert path.is_file() and not path.is_symlink(), 'Missing or linked source: ' + str(path)
    return sorted(paths)


def mathlib_imports(root, config):
    """Let Mathlib's cache tool compute transitive dependencies of focused import roots."""
    roots = verify.import_roots(config)
    modules = {'Mathlib.Tactic.Linter.Lint'}
    for path in source_paths(root, config):
        for module in verify.imported_modules(path.read_text()):
            assert verify.allowed_import(module, roots), 'Unapproved import: ' + module
            if module.startswith('Mathlib.'):
                modules.add(module)
    return sorted(modules)


def main():
    root = Path(__file__).resolve().parent.parent
    config = json.loads((root / 'verification.json').read_text())
    # Materialize exact locked dependencies; the workflow disables Mathlib's automatic
    # unscoped post-update cache fetch before this command.
    subprocess.run(['lake', 'env', 'lean', '--version'], cwd=root, check=True)
    manifest = verify.manifest_dependencies(
        json.loads((root / 'lake-manifest.json').read_text())['packages'])
    assert set(manifest) == set(config['public_dependencies']), 'Dependency coverage differs'
    for name, expected in config['public_dependencies'].items():
        package = manifest[name]
        assert package['type'] == 'git' and package['rev'] == expected['rev'], name
        assert package['url'] == expected['url'], name
        actual = subprocess.check_output(
            ['git', '-C', str(root / '.lake/packages' / name), 'rev-parse', 'HEAD'],
            text=True).strip()
        assert actual == expected['rev'], 'Checkout differs from the pinned revision: ' + name
    modules = mathlib_imports(root, config)
    print('Fetching Mathlib cache for', len(modules), 'focused import roots', flush=True)
    subprocess.run(['lake', 'exe', 'cache', 'get', *modules], cwd=root, check=True)


if __name__ == '__main__':
    main()
