"""Regression controls for acceptance failures; no Lean installation is needed."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name('verify.py')
spec = importlib.util.spec_from_file_location('standalone_verify', SCRIPT)
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def fixture_repository(root):
    """Create a minimal, isolated repository for mocked end-to-end verifier controls."""
    (root / 'scripts').mkdir(parents=True)
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
    (root / 'lakefile.lean').write_text('import Lake\n')
    (root / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
    config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
              'source_files': ['Fixture.lean'], 'audit_imports': ['Fixture'],
              'declarations': ['Fixture.identity'], 'public_dependencies': {}}
    (root / 'verification.json').write_text(json.dumps(config))
    (root / 'Fixture.lean').write_text(
        '/- Copyright (c) 2026 Adam Benenson. -/\nmodule\n/-! Fixture -/\n'
        'public section\nnamespace Fixture\ntheorem identity : True := by trivial\nend Fixture\n')


class VerificationControls(unittest.TestCase):
    def test_clean_plain_and_json_information(self):
        verify.check_diagnostics('Build completed successfully.\n')
        verify.check_diagnostics(json.dumps({'severity': 'information', 'data': 'checked'}),
                                 json_mode=True)

    def test_native_and_plain_diagnostic_rejection(self):
        for text in ['PANIC at kernel', 'panic: kernel', 'error: fixture',
                     'file.lean:3:2: warning: fixture']:
            with self.subTest(text=text), self.assertRaises(AssertionError):
                verify.check_diagnostics(text)

    def test_json_failures_rejected(self):
        for obj in [{'severity': 'error', 'data': 'fixture'},
                    {'severity': 'warning', 'data': 'fixture'},
                    {'severity': 'information', 'data': 'PANIC at kernel'},
                    {'severity': 'information', 'data': 'error: fixture'},
                    {'error': 'unrecognized diagnostic'},
                    {'severity': 'fatal', 'data': 'fixture'},
                    {'severity': 'information'}, []]:
            with self.subTest(obj=obj), self.assertRaises(AssertionError):
                verify.check_diagnostics(json.dumps(obj), json_mode=True)
        with self.assertRaises(AssertionError):
            verify.check_diagnostics('{"severity":"error"')
        with self.assertRaises(AssertionError):
            verify.check_diagnostics('unstructured output', json_mode=True)

    def test_every_import_is_returned(self):
        text = ('/- import Ignored.Comment -/\n'
                '  public import Mathlib.Data.Bool.Basic Private.Hidden\n'
                'import\n  Mathlib.Data.Nat.Basic\n  Private.Multiline\n'
                'namespace X\ndef s := "import Ignored.String"\nend X\n')
        self.assertEqual(verify.imported_modules(text),
                         ['Mathlib.Data.Bool.Basic', 'Private.Hidden',
                          'Mathlib.Data.Nat.Basic', 'Private.Multiline'])

    def test_unsupported_import_fails_closed(self):
        for text in ['import «Unsupported»', 'import\nnamespace X\nend X']:
            with self.subTest(text=text), self.assertRaises(AssertionError):
                verify.imported_modules(text)

    def test_optimized_python_refused(self):
        result = subprocess.run([sys.executable, '-O', str(SCRIPT), '--help'],
                                text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires enabled Python assertions', result.stderr)

    def test_manifest_quoted_package_names_use_plain_keys(self):
        mathlib = {'name': 'mathlib', 'rev': 'a' * 40}
        markov = {'name': '«finite-markov-kernels»', 'rev': 'b' * 40}
        dependencies = verify.manifest_dependencies([mathlib, markov])
        self.assertEqual(set(dependencies), {'mathlib', 'finite-markov-kernels'})
        self.assertIs(dependencies['mathlib'], mathlib)
        self.assertIs(dependencies['finite-markov-kernels'], markov)

    def test_manifest_invalid_and_colliding_package_names_refused(self):
        for name in ['', '../outside', 'a/b', 'a.b', '«a.b»', '«a b»', '«a»»',
                     '«nested«name»»', '«unclosed', 'unopened»', None, 42]:
            with self.subTest(name=name), self.assertRaises(AssertionError):
                verify.manifest_dependencies([{'name': name}])
        for names in [('mathlib', 'mathlib'),
                      ('finite-markov-kernels', '«finite-markov-kernels»')]:
            with self.subTest(names=names), self.assertRaisesRegex(
                    AssertionError, 'Duplicate manifest package name'):
                verify.manifest_dependencies([{'name': name} for name in names])

    def test_only_declared_dependency_module_roots_are_allowed(self):
        config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                  'public_dependencies': {'entropy': {'rev': 'a' * 40,
                      'url': 'https://github.com/example/entropy'}},
                  'dependency_modules': {'entropy': ['FiniteRelativeEntropy']}}
        roots = verify.import_roots(config)
        for module in ['Fixture', 'Fixture.Basic', 'FixtureExamples.Basic',
                       'FiniteRelativeEntropy', 'FiniteRelativeEntropy.GibbsVariational',
                       'Mathlib.Data.Real.Basic']:
            self.assertTrue(verify.allowed_import(module, roots), module)
        for module in ['Private.Hidden', 'FiniteRelativeEntropyOther.Basic', 'Mathlib']:
            self.assertFalse(verify.allowed_import(module, roots), module)

    def test_dependency_module_without_exact_public_pin_is_refused(self):
        config = {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                  'public_dependencies': {}, 'dependency_modules': {'entropy': ['Entropy']}}
        with self.assertRaisesRegex(AssertionError, 'Unpinned dependency module'):
            verify.import_roots(config)
        for pin in [{}, {'rev': 'main', 'url': 'https://github.com/example/entropy'},
                    {'rev': 'a' * 40, 'url': '/private/local/entropy'}]:
            config['public_dependencies'] = {'entropy': pin}
            with self.subTest(pin=pin), self.assertRaises(AssertionError):
                verify.import_roots(config)

    def test_authored_artifacts_removed_without_touching_other_outputs(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            library = root / '.lake/build/lib/lean'
            dependency = root / '.lake/packages/mathlib/.lake/build/lib/lean/Fixture.olean'
            dependency.parent.mkdir(parents=True)
            dependency.write_bytes(b'dependency cache')
            library.mkdir(parents=True)
            unrelated = library / 'Unrelated.olean'
            unrelated.write_bytes(b'unrelated output')
            stale = [library / ('Fixture' + suffix) for suffix in
                     ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean.hash', '.trace')]
            for path in stale:
                path.write_bytes(b'stale authored artifact')
            removed = verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(set(removed), {str(path.relative_to(root)) for path in stale})
            self.assertTrue(all(not path.exists() for path in stale))
            self.assertEqual(dependency.read_bytes(), b'dependency cache')
            self.assertEqual(unrelated.read_bytes(), b'unrelated output')

    def test_linked_artifact_directory_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            external = Path(temp) / 'external'
            external.mkdir()
            artifact = external / 'Fixture.olean'
            artifact.write_bytes(b'preserve external artifact')
            library = root / '.lake/build/lib/lean'
            library.parent.mkdir(parents=True)
            library.symlink_to(external, target_is_directory=True)
            with self.assertRaisesRegex(AssertionError, 'Linked authored artifact directory'):
                verify.clear_authored_artifacts(root, ['Fixture.lean'])
            self.assertEqual(artifact.read_bytes(), b'preserve external artifact')

    def test_cached_authored_artifact_is_removed_before_exact_build(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            fixture_repository(root)
            stale = root / '.lake/build/lib/lean/Fixture.olean'
            stale.parent.mkdir(parents=True)
            stale.write_bytes(b'invalid cached authored artifact')

            def fake_run(command, **kwargs):
                if command == ['lake', 'env', 'lean', '--version']:
                    output = 'Lean (version 4.35.0, fixture)'
                elif 'build' in command:
                    self.assertFalse(stale.exists(), 'Exact build consumed a cached author artifact')
                    stale.write_bytes(b'fresh authored artifact')
                    output = 'Build completed successfully.'
                elif command[-1].endswith('axioms.lean'):
                    output = json.dumps({'severity': 'information',
                                         'data': "'Fixture.identity' depends on axioms: [propext]"})
                else:
                    replay = Path(command[-1]).read_text()
                    self.assertIn('module\nimport Mathlib.Tactic.Linter.Lint\n', replay)
                    self.assertEqual(
                        replay.replace('import Mathlib.Tactic.Linter.Lint\n', '', 1)
                        .removesuffix('\n#lint docBlame docBlameThm\n'),
                        (root / 'Fixture.lean').read_text())
                    output = json.dumps({'severity': 'information',
                                         'data': '-- All linting checks passed! with 16 linters'})
                return SimpleNamespace(returncode=0, stdout=output)

            evidence = Path(temp) / 'evidence'
            with patch.object(verify, '__file__', str(root / 'scripts/verify.py')), \
                 patch.object(sys, 'argv', [str(SCRIPT), '--evidence-dir', str(evidence)]), \
                 patch.object(verify.subprocess, 'run', side_effect=fake_run):
                verify.main()
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'passed')
            self.assertEqual(record['removed_authored_artifacts'],
                             ['.lake/build/lib/lean/Fixture.olean'])
            self.assertEqual(stale.read_bytes(), b'fresh authored artifact')

    def test_zero_exit_exact_build_error_rejected_end_to_end(self):
        def fake_run(command, **kwargs):
            if command == ['lake', 'env', 'lean', '--version']:
                output = 'Lean (version 4.35.0, fixture)'
            else:
                self.assertIn('build', command)
                output = json.dumps({'severity': 'error', 'data': 'synthetic exact-build failure'})
            return SimpleNamespace(returncode=0, stdout=output)

        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / 'repo'
            fixture_repository(root)
            evidence = Path(temp) / 'failed-run'
            with patch.object(verify, '__file__', str(root / 'scripts/verify.py')), \
                 patch.object(sys, 'argv', [str(SCRIPT), '--evidence-dir', str(evidence)]), \
                 patch.object(verify.subprocess, 'run', side_effect=fake_run):
                with self.assertRaises(AssertionError):
                    verify.main()
            record = json.loads((evidence / 'qualification.json').read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual(record['stages'][-1]['name'], 'exact-build')
            self.assertEqual(record['stages'][-1]['exit_code'], 0)
            self.assertIn('synthetic exact-build failure', record['failure'])


if __name__ == '__main__':
    unittest.main()
