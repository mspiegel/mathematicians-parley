#!/usr/bin/env python3
"""Nothing an elaborated proof takes as stated goes unrecorded.

`GOALS.md` decision 17: a step the elaborator cannot build enters the
archive as an axiom and weakens what the archive proves, so it is a defect
and the gate is red, or `ELABORATION.md` records it — the step, why it is
not built, and what would build it. A list in the elaborated file's header
says what the file assumes, and is not a record: nothing makes anyone read
it.

So every `$a` in a file under `elaboration/proof/` must be named in the
section "Steps taken as stated" of `ELABORATION.md`, and every statement
named there must still be one a file takes. The second keeps the record
from outliving what it records.

Reads what the build wrote and builds nothing, as the other stages do.

Usage:  parley/assumed.py [root]
"""
import re
import sys
from pathlib import Path

AXIOM = re.compile(r'(?m)^\s*(\S+)\s+\$a\s')
# A record starts at the margin; the indented form shown in the section is
# its example, not a record.
RECORD = re.compile(r'(?m)^- `(elaboration/proof/[^`]+\.mm)` `([^`]+)`:')
SECTION = '### Steps taken as stated'


def recorded(text):
    """(file, label) pairs the section of `ELABORATION.md` names."""
    _before, found, after = text.partition(SECTION)
    if not found:
        return None
    body = re.split(r'(?m)^#{2,3} ', after, maxsplit=1)[0]
    return set(RECORD.findall(body))


def taken(root):
    """(file, label) pairs the elaborated proofs take as stated."""
    out = set()
    for path in sorted((root / 'elaboration' / 'proof').rglob('*.mm')):
        rel = str(path.relative_to(root))
        out |= {(rel, label) for label in AXIOM.findall(path.read_text())}
    return out


def main(argv):
    root = Path(argv[1]) if len(argv) > 1 \
        else Path(__file__).resolve().parent.parent
    written = recorded((root / 'ELABORATION.md').read_text())
    if written is None:
        print(f'ELABORATION.md has no section "{SECTION[4:]}"')
        return 1
    found = taken(root)
    problems = [f'{rel}: {label} is taken as stated, and ELABORATION.md '
                f'does not record it' for rel, label in sorted(found - written)]
    problems += [f'ELABORATION.md records {label} in {rel}, which that file '
                 f'no longer takes as stated'
                 for rel, label in sorted(written - found)]
    for one in problems:
        print(one)
    if problems:
        return 1
    print('nothing is taken as stated that ELABORATION.md does not record')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
