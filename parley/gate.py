#!/usr/bin/env python3
"""Everything that must be green before a commit.

Five things, in the order that fails fastest: the lint settings in
`ruff.toml`, the checker over the whole corpus, the planted defects that prove
the checker still catches things, every set.mm label the database names, and
a verifier over every proof the elaborator has written. Any one of them
failing fails the gate.

The last is the only one that is evidence the elaborator is right rather than
consistent. The four before it read the corpus against itself or against a
list of names; a proof that assumes nothing and proves the wrong thing passes
all four, and has.

Three of them need something this repository does not carry, and none of the
three is vendored. ruff: if it is missing, say

    pip install ruff

or run it from a virtual environment, and the gate looks for it on PATH.
set.mm is 51 MB and belongs to metamath, so it is not committed either; say
where it is with `SET_MM`, or leave a copy or a link at the root of the
working tree. mmverify.py belongs to metamath too; say where it is with
`MMVERIFY`, or leave a copy or a link at the root. A gate that skipped any of
them would be saying green about a thing it had not looked at.

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
    if not run('set.mm labels',
               [sys.executable, str(ROOT / 'parley' / 'labels.py')]):
        failed.append('set.mm labels')
    if not run('the proofs verify',
               [sys.executable, str(ROOT / 'parley' / 'verify.py')]):
        failed.append('the proofs verify')

    print()
    if failed:
        print(f'NOT GREEN: {", ".join(failed)}')
        return 1
    print('green')
    return 0


if __name__ == '__main__':
    sys.exit(main())
