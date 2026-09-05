import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('build_web', Path(__file__).with_name('build_web.py'))
build_web = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build_web)


class WebBundleTests(unittest.TestCase):
    def test_retention_survives_two_updates_without_replacing_the_new_page(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def make(value, name, previous=()):
                return build_web.bundle({'index.html': b'<span>Cetacea</span><script src="./app.js"></script>',
                                         'app.js': value}, root / name, previous)
            first = make(b'first', 'first')
            second = make(b'second', 'second', [root / 'first'])
            third = make(b'third', 'third', [root / 'second', root / 'first'])
            plain = make(b'third', 'plain')
            self.assertEqual(third['build'], plain['build'])
            self.assertEqual((root / 'third/index.html').read_bytes(), (root / 'plain/index.html').read_bytes())
            for manifest, value in [(first, b'first'), (second, b'second'), (third, b'third')]:
                self.assertEqual((root / 'third/assets' / manifest['build'] / 'app.js').read_bytes(), value)
            for name, digest in third['files'].items():
                self.assertEqual(hashlib.sha256((root / 'third' / name).read_bytes()).hexdigest(), digest)
            self.assertEqual(first, json.loads((root / 'first/build.json').read_text()))

    def test_retention_rejects_corruption_traversal_and_symlinks_atomically(self):
        for mode in ('corrupt', 'traversal', 'symlink', 'missing'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                old = root / 'old'
                inputs = {'index.html': b'<span>Cetacea</span>', 'app.js': b'original'}
                manifest = build_web.bundle(inputs, old)
                asset = old / 'assets' / manifest['build'] / 'app.js'
                if mode == 'corrupt':
                    asset.write_bytes(b'changed')
                elif mode == 'traversal':
                    manifest['files']['../outside'] = hashlib.sha256(b'outside').hexdigest()
                    (root / 'outside').write_bytes(b'outside')
                    (old / 'build.json').write_text(json.dumps(manifest))
                elif mode == 'symlink':
                    asset.unlink()
                    (root / 'outside').write_bytes(b'original')
                    asset.symlink_to(root / 'outside')
                else:
                    asset.unlink()
                with self.assertRaises((ValueError, OSError)):
                    build_web.bundle(inputs, root / 'new', [old])
                self.assertFalse((root / 'new').exists())
                self.assertEqual(list(root.glob('.cetacea-web-*')), [])

    def test_retention_ignores_unlisted_files_and_rejects_conflicting_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = {'index.html': b'<span>Cetacea</span>', 'app.js': b'original'}
            manifest = build_web.bundle(inputs, root / 'old')
            (root / 'old/unlisted.txt').write_text('do not copy')
            combined = build_web.bundle(inputs, root / 'same', [root / 'old'])
            self.assertEqual(manifest, combined)
            self.assertFalse((root / 'same/unlisted.txt').exists())
            name = f"assets/{manifest['build']}/app.js"
            (root / 'old' / name).write_bytes(b'conflicting')
            manifest['files'][name] = hashlib.sha256(b'conflicting').hexdigest()
            (root / 'old/build.json').write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, 'conflicts with current build'):
                build_web.bundle(inputs, root / 'new', [root / 'old'])
            self.assertFalse((root / 'new').exists())
            self.assertEqual(list(root.glob('.cetacea-web-*')), [])

    def test_all_local_module_and_worker_urls_receive_one_version(self):
        text = '''import './student-work.mjs?v=2'; new URL('./checker-worker.js', import.meta.url); fetch("./pkg/cetacea_wasm.wasm");'''
        result = build_web.version_assets(text, ['student-work.mjs', 'checker-worker.js', 'pkg/cetacea_wasm.wasm'], 'abc')
        self.assertEqual(result.count('?build=abc'), 3)
        self.assertNotIn('?v=2', result)

    def test_bundle_is_reproducible_and_preserves_existing_output(self):
        inputs = {'index.html': b'<span>Cetacea</span><script src="./app.js"></script>',
                  'app.js': b"import './helper.mjs?v=2';", 'helper.mjs': b'export const value = 1;',
                  'checker-worker.js': b'const wasmPaths = ["./pkg/cetacea_wasm.wasm", "../target/old.wasm"];',
                  'pkg/cetacea_wasm.wasm': b'wasm fixture'}
        with tempfile.TemporaryDirectory() as directory:
            first, second = Path(directory) / 'first', Path(directory) / 'second'
            manifest = build_web.bundle(inputs, first)
            self.assertEqual(manifest, build_web.bundle(inputs, second))
            for path in first.rglob('*'):
                if path.is_file(): self.assertEqual(path.read_bytes(), (second / path.relative_to(first)).read_bytes())
            assets = first / 'assets' / manifest['build']
            self.assertNotIn('../target', (assets / 'checker-worker.js').read_text())
            self.assertIn('?build=' + manifest['build'], (assets / 'checker-worker.js').read_text())
            self.assertIn('./assets/' + manifest['build'] + '/app.js', (first / 'index.html').read_text())
            self.assertFalse((first / 'app.js').exists())
            original = (first / 'build.json').read_bytes()
            with self.assertRaises(ValueError): build_web.bundle(inputs, first)
            self.assertEqual(original, (first / 'build.json').read_bytes())
            changed = dict(inputs, **{'helper.mjs': b'changed'})
            third = Path(directory) / 'third'
            changed_manifest = build_web.bundle(changed, third)
            self.assertNotEqual(manifest['build'], changed_manifest['build'])
            self.assertFalse((third / 'assets' / manifest['build']).exists(), 'An old asset URL must not resolve to new bytes')


if __name__ == '__main__':
    unittest.main()
