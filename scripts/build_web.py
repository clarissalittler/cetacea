#!/usr/bin/env python3
"""Build a self-contained, identified web distribution without publishing it."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def version_assets(text, asset_names, build_id):
    names = '|'.join(re.escape(name) for name in sorted(asset_names, key=len, reverse=True))
    return re.sub(r'(\./(?:' + names + r'))(?:\?[^\s\"\'`<>]*)?(?=[\"\'`])',
                  lambda match: match[1] + '?build=' + build_id, text)


def retained_assets(previous):
    """Read only manifest-listed, hash-verified assets from prior bundles."""
    assets = {}
    for directory in previous:
        directory = Path(directory)
        manifest_path = directory / 'build.json'
        if directory.is_symlink() or manifest_path.is_symlink():
            raise ValueError('Previous bundles must not use symlinks.')
        manifest = json.loads(manifest_path.read_text())
        build = manifest.get('build', '')
        if (manifest.get('format') != 'cetacea-web-build'
                or manifest.get('version') != 1
                or not isinstance(build, str) or not re.fullmatch('[0-9a-f]{64}', build)
                or not isinstance(manifest.get('files'), dict)):
            raise ValueError(f'Invalid previous build manifest: {directory}')
        files = manifest['files']
        if 'index.html' not in files or not any(name.startswith(f'assets/{build}/') for name in files):
            raise ValueError(f'Incomplete previous build manifest: {directory}')
        for name, expected in files.items():
            parts = PurePosixPath(name).parts
            if (not parts or '/'.join(parts) != name or '\\' in name
                    or any(part in ('.', '..') for part in parts)
                    or (name != 'index.html' and (len(parts) < 3 or parts[0] != 'assets'
                        or not re.fullmatch('[0-9a-f]{64}', parts[1])))):
                raise ValueError(f'Invalid retained asset path: {name}')
            path = directory
            for part in parts:
                path = path / part
                if path.is_symlink():
                    raise ValueError(f'Symlink in retained asset path: {name}')
            data = path.read_bytes()
            if hashlib.sha256(data).hexdigest() != expected:
                raise ValueError(f'Previous asset hash mismatch: {name}')
            if name != 'index.html':
                if name in assets and assets[name] != data:
                    raise ValueError(f'Conflicting retained asset: {name}')
                assets[name] = data
    return assets


def bundle(inputs, output, previous=()):
    """Write one immutable bundle; never replace an existing distribution."""
    if output.exists():
        raise ValueError(f'Output already exists: {output}. Choose a new output directory.')
    retained = retained_assets(previous)
    digest = hashlib.sha256()
    digest.update(Path(__file__).read_bytes())
    for name, data in sorted(inputs.items()):
        digest.update(name.encode() + b'\0' + hashlib.sha256(data).digest())
    build_id = digest.hexdigest()
    def asset_path(name):
        return name if name == 'index.html' else f'assets/{build_id}/{name}'
    output.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix='.cetacea-web-', dir=output.parent))
    try:
        for name, data in sorted(inputs.items()):
            destination = stage / asset_path(name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            if name.endswith(('.js', '.mjs', '.html', '.css')):
                text = data.decode('utf-8')
                if name == 'checker-worker.js':
                    text, count = re.subn(r'const wasmPaths = \[[^\n]*\];',
                        'const wasmPaths = ["./pkg/cetacea_wasm.wasm"];', text)
                    if count != 1:
                        raise ValueError('Worker loader changed; update the bundle builder.')
                text = version_assets(text, inputs.keys(), build_id)
                if name == 'index.html':
                    for asset in inputs:
                        if asset != 'index.html':
                            text = text.replace('./' + asset + '?build=', './' + asset_path(asset) + '?build=')
                    brand = '<span>Cetacea</span>'
                    if text.count(brand) != 1:
                        raise ValueError('Editor brand changed; update the build label insertion.')
                    text = text.replace(brand, brand + f'<small title="{build_id}">Build {build_id[:12]}</small>')
                data = text.encode('utf-8')
            destination.write_bytes(data)
        manifest = {'format': 'cetacea-web-build', 'version': 1, 'build': build_id,
                    'files': {asset_path(name): hashlib.sha256((stage / asset_path(name)).read_bytes()).hexdigest() for name in sorted(inputs)}}
        for name, data in sorted(retained.items()):
            destination = stage / name
            if destination.exists() and destination.read_bytes() != data:
                raise ValueError(f'Retained asset conflicts with current build: {name}')
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            manifest['files'][name] = hashlib.sha256(data).hexdigest()
        manifest['files'] = dict(sorted(manifest['files'].items()))
        (stage / 'build.json').write_text(json.dumps(manifest, indent=2) + '\n')
        # No partial build is exposed at the requested output path.
        stage.rename(output)
    except BaseException:
        shutil.rmtree(stage)
        raise
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='New output directory; existing directories are preserved')
    parser.add_argument('--retain-from', type=Path, action='append', default=[],
                        help='Previous local bundle whose verified assets to retain; repeatable')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error('Output already exists; choose a new directory.')
    subprocess.run(['cargo', 'build', '-p', 'cetacea_wasm', '--target', 'wasm32-unknown-unknown', '--release'], cwd=ROOT, check=True)
    inputs = {path.name: path.read_bytes() for path in (ROOT / 'web').iterdir()
              if path.is_file() and path.suffix in ('.html', '.css', '.js', '.mjs')}
    inputs['pkg/cetacea_wasm.wasm'] = (ROOT / 'target/wasm32-unknown-unknown/release/cetacea_wasm.wasm').read_bytes()
    manifest = bundle(inputs, output, args.retain_from)
    print(f"Built {manifest['build']} at {output}")


if __name__ == '__main__':
    main()
