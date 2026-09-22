#!/usr/bin/env python3
"""Every elaborated proof, checked by a verifier rather than by this project.

The checker reads the readable layer and the elaborator writes Metamath from
it. Neither is evidence that what came out is a proof: an elaborator that
emits a wrong step emits it confidently, and the assumption count at the head
of each file reports a proof that assumes nothing whether or not it proves
what it claims. Only a verifier settles that, and it is the one tool here
that was not written for this project.

Verifying the proofs one at a time costs about eighteen seconds each, and
almost all of it is reading set.mm. `mmverify.py` resolves an inclusion
against the working directory and keeps the set of files it has opened, so
including them all from one file reads set.mm once and the nine cost
eighteen seconds together.

Which files there are comes from `parley/build.py`, which is where every
generated file is listed. Reading a directory instead would be simpler and
wrong: they do not all sit in one, and two of them share a basename with a
hand-written proof that is not among them, which the flat directory below
could not hold at once.

Which of them to include is read off the inclusions rather than listed: a
proof that nothing else includes is a root, and including every root reaches
everything. A tenth proof is covered the day it is written, where a list of
roots in a file would leave the gate green and the new proof unread.

mmverify.py belongs to metamath and is not vendored, for the reason ruff and
set.mm are not: say where it is with `MMVERIFY`, or leave a copy or a link at
the root of the working tree.

Usage:  parley/verify.py [set.mm]
Exits non-zero when a proof does not verify.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from build import verified
from library import where_set_mm

ROOT = Path(__file__).resolve().parent.parent
INCLUDE = re.compile(r'\$\[\s*(\S+)\s*\$\]')
# A labelled `$p`, which is what there is one of per theorem proved.
PROVES = re.compile(r'(?m)^\s*(\S+)\s+\$p\s')


def where_mmverify(argv):
    """The verifier, said on the command line, in the environment, or here."""
    for said in (argv[1] if len(argv) > 1 else None,
                 os.environ.get('MMVERIFY'), ROOT / 'mmverify.py',
                 shutil.which('mmverify.py')):
        if said and Path(said).exists():
            return Path(said)
    return None


def roots(built):
    """The files nothing else includes, which reach everything between them.

    Read off the inclusions so that a proof added later is covered without
    this being edited. set.mm is included too and is not one of these files,
    so it falls out of the difference on its own.
    """
    here = {p.name: p for p in built}
    included = set()
    for path in built:
        included |= {name for name in INCLUDE.findall(path.read_text())
                     if name in here}
    return sorted(set(here) - included)


def main(argv):
    verifier = where_mmverify(argv)
    if verifier is None:
        print('mmverify.py not found; say where it is with MMVERIFY, or '
              'leave a copy or a link at the root of the working tree')
        return 2
    library = where_set_mm(argv)
    if library is None:
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2
    built = verified()
    missing = [p for p in built if not p.exists()]
    if missing:
        for path in missing:
            print(f'not built: {path.relative_to(ROOT)}')
        print('\nrun parley/build.py')
        return 2

    top = roots(built)
    proved = sum(len(PROVES.findall(p.read_text())) for p in built)
    print(f'{proved} proofs in {len(built)} files, reached from '
          f'{", ".join(top)}')

    # An inclusion resolves against the working directory, so everything has
    # to sit in one place. Linked rather than copied: set.mm is 51 MB.
    with tempfile.TemporaryDirectory() as tmp:
        where = Path(tmp)
        for path in built:
            (where / path.name).symlink_to(path)
        (where / library.name).symlink_to(library.resolve())
        if library.name != 'set.mm':
            (where / 'set.mm').symlink_to(library.resolve())
        joined = where / 'everything.mm'
        joined.write_text(''.join(f'$[ {name} $]\n' for name in top))
        began = time.monotonic()
        done = subprocess.run([sys.executable, str(verifier), 'everything.mm'],
                              cwd=where)
        spent = time.monotonic() - began

    if done.returncode != 0:
        print(f'\n{verifier.name} rejected a proof')
        return 1
    print(f'\nall {proved} verify, in {spent:.0f}s')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
