import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'private_dependencies', ROOT / 'scripts/prepare_private_dependencies.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class PrivateDependencyTests(unittest.TestCase):
    def fixture(self, temp):
        root = Path(temp)
        shutil.copytree(ROOT / 'vendor', root / 'vendor')
        shutil.copyfile(ROOT / 'lake-manifest.json', root / 'lake-manifest.json')
        return root

    def test_offline_materialization_and_reuse(self):
        with tempfile.TemporaryDirectory() as temp:
            root = self.fixture(temp)
            module.prepare(root)
            module.prepare(root)
            lock = json.loads((root / 'vendor/dependencies.json').read_text())
            for name, expected in lock.items():
                target = root / '.lake/packages' / name
                self.assertEqual(module.git(target, 'rev-parse', 'HEAD'), expected['rev'])
                self.assertEqual(module.git(target, 'remote', 'get-url', 'origin'), expected['url'])
            first = next(iter(lock))
            target = root / '.lake/packages' / first
            (target / 'README.md').write_text('dirty fixture')
            with self.assertRaisesRegex(ValueError, 'Dirty dependency'):
                module.prepare(root)

    def test_corrupt_bundle_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = self.fixture(temp)
            bundle = next((root / 'vendor').glob('*.bundle'))
            bundle.write_bytes(b'corrupt bundle')
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                module.prepare(root)
            self.assertFalse((root / '.lake/packages' / bundle.stem).exists())

    def test_manifest_pin_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = self.fixture(temp)
            path = root / 'vendor/dependencies.json'
            lock = json.loads(path.read_text())
            lock[next(iter(lock))]['rev'] = '0' * 40
            path.write_text(json.dumps(lock))
            with self.assertRaisesRegex(ValueError, 'pin differs'):
                module.prepare(root)


if __name__ == '__main__':
    unittest.main()
