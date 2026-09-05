#!/usr/bin/env python3
"""Run a checker with wall-time, address-space and captured-output limits (Unix)."""
import argparse
import json
import math
import os
import resource
import selectors
import signal
import subprocess
import sys
import time


def run_limited(command, seconds=30, memory_mib=1024, output_mib=8):
    if not all(math.isfinite(value) and value > 0 for value in (seconds, memory_mib, output_mib)):
        raise ValueError('Resource limits must be positive')
    def limits():
        memory = memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True, preexec_fn=limits)
    deadline = time.monotonic() + seconds
    captured = [bytearray(), bytearray()]
    size = 0
    failure = None
    selector = selectors.DefaultSelector()
    for index, stream in enumerate([process.stdout, process.stderr]):
        os.set_blocking(stream.fileno(), False)
        selector.register(stream, selectors.EVENT_READ, index)
    try:
        while selector.get_map() or process.poll() is None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                failure = ('time', f'Checker exceeded {seconds:g} seconds')
                break
            for key, _ in selector.select(min(remaining, 0.1)):
                data = os.read(key.fileobj.fileno(), 65536)
                if not data:
                    selector.unregister(key.fileobj)
                    continue
                size += len(data)
                if size > output_mib * 1024 * 1024:
                    failure = ('output', f'Checker output exceeded {output_mib:g} MiB')
                    break
                captured[key.data].extend(data)
            if failure:
                break
        if failure:
            # Kill the whole checker job, including descendants holding pipes open.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        code = process.wait()
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        selector.close()
        process.stdout.close()
        process.stderr.close()
    if failure:
        kind, message = failure
        return 124 if kind == 'time' else 125, json.dumps({'ok': False, 'resource_limit': {'kind': kind, 'message': message}}).encode() + b'\n', b''
    if code < 0:
        return 125, json.dumps({'ok': False, 'checker_failure': {'signal': -code, 'message': 'Checker terminated by a signal; no grading result is available'}}).encode() + b'\n', bytes(captured[1])
    return code, bytes(captured[0]), bytes(captured[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=30)
    parser.add_argument('--memory-mib', type=int, default=1024)
    parser.add_argument('--output-mib', type=float, default=8)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('Provide a checker command after --')
    try:
        code, stdout, stderr = run_limited(command, args.seconds, args.memory_mib, args.output_mib)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(json.dumps({'ok': False, 'runner_error': str(error)}))
        raise SystemExit(125)
    sys.stdout.buffer.write(stdout)
    sys.stderr.buffer.write(stderr)
    raise SystemExit(code)


if __name__ == '__main__':
    main()
