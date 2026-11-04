"""Materialize exactly pinned private dependencies from verified Git bundles."""
import hashlib
import json
from pathlib import Path
import re
import subprocess


def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()


def prepare(root):
    entries = json.loads((root / 'lake-manifest.json').read_text())['packages']
    manifest = {p['name'].strip('«»'): p for p in entries}
    lock = json.loads((root / 'vendor/dependencies.json').read_text())
    for name, expected in lock.items():
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', name):
            raise ValueError('Invalid dependency name')
        entry = manifest[name]
        if entry['rev'] != expected['rev'] or entry['url'] != expected['url']:
            raise ValueError('Bundle pin differs from Lake manifest: ' + name)
        bundle = root / 'vendor' / (name + '.bundle')
        if hashlib.sha256(bundle.read_bytes()).hexdigest() != expected['sha256']:
            raise ValueError('Dependency bundle hash mismatch: ' + name)
        target = root / '.lake/packages' / name
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git', 'clone', '--no-checkout', str(bundle), str(target)], check=True)
            subprocess.run(['git', '-C', str(target), 'checkout', '--detach', expected['rev']],
                           check=True)
            subprocess.run(['git', '-C', str(target), 'remote', 'set-url', 'origin', entry['url']],
                           check=True)
        if git(target, 'rev-parse', 'HEAD') != expected['rev']:
            raise ValueError('Dependency checkout pin mismatch: ' + name)
        if git(target, 'status', '--porcelain', '--untracked-files=no'):
            raise ValueError('Dirty dependency checkout: ' + name)
        print(name, expected['rev'], 'verified')


if __name__ == '__main__':
    prepare(Path(__file__).resolve().parents[1])
