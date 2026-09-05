#!/usr/bin/env python3
"""Serve a local, cache-disabled old-to-new bundle transition test; never deploy."""
import argparse
import json
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import secrets
from urllib.parse import urlsplit

from build_web import ROOT, retained_assets


def make_server(old, new, port):
    old, new = Path(old).resolve(), Path(new).resolve()
    old_assets = retained_assets([old])
    new_assets = retained_assets([new])
    if any(new_assets.get(name) != data for name, data in old_assets.items()):
        raise ValueError('New bundle must retain every old asset unchanged.')
    old_id = json.loads((old / 'build.json').read_text())['build']
    new_id = json.loads((new / 'build.json').read_text())['build']
    if old_id == new_id:
        raise ValueError('The test requires two distinct build IDs.')
    state = {'updated': False, 'requests': []}
    token = secrets.token_urlsafe(32)

    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=str(old), **kwargs)

        def end_headers(self):
            self.send_header('Cache-Control', 'no-store')
            super().end_headers()

        def respond(self, data, content_type='application/json'):
            self.send_response(200)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            path = urlsplit(self.path).path
            if path == '/__bundle-test__/':
                self.respond((ROOT / 'web/tests/bundle-update.html').read_bytes(), 'text/html; charset=utf-8')
            elif path == '/__bundle-test__/editor':
                self.respond((ROOT / 'web/tests/editor-update.html').read_bytes(), 'text/html; charset=utf-8')
            elif path == '/__bundle-test__/state':
                self.respond(json.dumps(dict(state, old=old_id, new=new_id, token=token)).encode())
            elif path == '/__bundle-test__/fixtures':
                self.respond((ROOT / 'web/tests/assignment-parity.json').read_bytes())
            else:
                self.directory = str(new if state['updated'] else old)
                state['requests'].append({'path': path, 'updated': state['updated']})
                super().do_GET()

        def do_POST(self):
            if self.path != '/__bundle-test__/update' or self.headers.get('X-Test-Token') != token:
                self.send_error(403)
                return
            state['updated'] = True
            self.respond(b'{"updated":true}')

    return ThreadingHTTPServer(('127.0.0.1', port), Handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, required=True)
    parser.add_argument('--new', type=Path, required=True)
    parser.add_argument('--port', type=int, default=8766)
    args = parser.parse_args()
    with make_server(args.old, args.new, args.port) as server:
        print(f'Open http://localhost:{server.server_port}/__bundle-test__/ (restart server to repeat)', flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == '__main__':
    main()
