"""Offline controls for cache scope and public dependency coverage."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import call, patch

import fetch_mathlib_cache as cache


class CacheScopeControls(unittest.TestCase):
    def fixture(self, root):
        (root / 'Fixture.lean').write_text(
            '/- import Mathlib.Hidden -/\nmodule\npublic import\n Mathlib.Data.Bool.Basic\n'
            'namespace Fixture\ndef text := "import Mathlib.Hidden"\nend Fixture\n')
        return {'root_module': 'Fixture', 'examples_module': 'FixtureExamples',
                'source_files': ['Fixture.lean'], 'public_dependencies': {}}

    def test_focused_multiline_imports_and_linter_are_included(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            self.assertEqual(cache.mathlib_imports(root, config),
                             ['Mathlib.Data.Bool.Basic', 'Mathlib.Tactic.Linter.Lint'])

    def test_public_dependency_sources_extend_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            config['public_dependencies']['public-library'] = {
                'url': 'https://github.com/example/public-library', 'rev': 'a' * 40}
            config['dependency_modules'] = {'public-library': ['PublicLibrary']}
            provider = root / '.lake/packages/public-library/PublicLibrary'
            provider.mkdir(parents=True)
            (provider / 'Basic.lean').write_text(
                'module\npublic import Mathlib.Data.Nat.Basic\n')
            self.assertIn('Mathlib.Data.Nat.Basic', cache.mathlib_imports(root, config))

    def test_bare_mathlib_and_private_imports_are_rejected(self):
        for module in ['Mathlib', 'Private.Internal']:
            with self.subTest(module=module), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                config = self.fixture(root)
                (root / 'Fixture.lean').write_text('import ' + module + '\n')
                with self.assertRaises(AssertionError):
                    cache.mathlib_imports(root, config)

    def test_missing_dependency_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.fixture(root)
            config['public_dependencies']['public-library'] = {
                'url': 'https://github.com/example/public-library', 'rev': 'a' * 40}
            config['dependency_modules'] = {'public-library': ['PublicLibrary']}
            with self.assertRaisesRegex(AssertionError, 'Missing pinned dependency'):
                cache.mathlib_imports(root, config)


    def main_fixture(self, root):
        config = self.fixture(root)
        dependency = {'url': 'https://github.com/leanprover-community/mathlib4',
                      'rev': 'a' * 40}
        config['public_dependencies']['mathlib'] = dependency
        (root / 'verification.json').write_text(json.dumps(config))
        manifest = {'packages': [dict(name='mathlib', type='git', **dependency)]}
        (root / 'lake-manifest.json').write_text(json.dumps(manifest))
        return manifest

    def test_main_uses_only_focused_roots_after_pin_checks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.main_fixture(root)
            with patch.object(cache, '__file__', str(root / 'scripts/fetch_mathlib_cache.py')), \
                 patch.object(cache.subprocess, 'run') as run, \
                 patch.object(cache.subprocess, 'check_output', return_value='a' * 40):
                cache.main()
            self.assertEqual(run.call_args_list, [
                call(['lake', 'env', 'lean', '--version'], cwd=root, check=True),
                call(['lake', 'exe', 'cache', 'get', 'Mathlib.Data.Bool.Basic',
                      'Mathlib.Tactic.Linter.Lint'], cwd=root, check=True)])

    def test_main_refuses_manifest_or_checkout_pin_mismatch(self):
        for mismatch in ['manifest', 'checkout']:
            with self.subTest(mismatch=mismatch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = self.main_fixture(root)
                if mismatch == 'manifest':
                    manifest['packages'][0]['rev'] = 'b' * 40
                    (root / 'lake-manifest.json').write_text(json.dumps(manifest))
                with patch.object(cache, '__file__', str(root / 'scripts/fetch_mathlib_cache.py')), \
                     patch.object(cache.subprocess, 'run') as run, \
                     patch.object(cache.subprocess, 'check_output', return_value='b' * 40), \
                     self.assertRaises(AssertionError):
                    cache.main()
                self.assertEqual(run.call_args_list,
                                 [call(['lake', 'env', 'lean', '--version'],
                                       cwd=root, check=True)])

if __name__ == '__main__':
    unittest.main()
