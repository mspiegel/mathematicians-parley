#!/usr/bin/env python3
"""Everything that must be green before a commit.

Three things, in the order that fails fastest: the lint settings in
`ruff.toml`, the checker over the whole corpus, and the planted defects that
prove the checker still catches things. Any one of them failing fails the gate.

ruff is not vendored and not installed by this script. If it is missing, say

    pip install ruff

or run it from a virtual environment; the gate looks for it on PATH.

Usage:  parley/gate.py
Exits non-zero when anything is not green.
"""
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(what, argv):
    # Flushed, or this heading arrives after the output it introduces.
    print(f'\n=== {what}', flush=True)
    return subprocess.run(argv, cwd=ROOT).returncode == 0


def main():
    failed = []

    ruff = shutil.which('ruff')
    if ruff is None:
        print('\n=== ruff\nnot on PATH; install it with `pip install ruff`')
        failed.append('ruff')
    elif not run('ruff', [ruff, 'check', '.']):
        failed.append('ruff')

    if not run('checker', [sys.executable, str(ROOT / 'parley' / 'check.py')]):
        failed.append('checker')
    if not run('planted defects',
               [sys.executable, str(ROOT / 'parley' / 'test_check.py')]):
        failed.append('planted defects')

    print()
    if failed:
        print(f'NOT GREEN: {", ".join(failed)}')
        return 1
    print('green')
    return 0


if __name__ == '__main__':
    sys.exit(main())
