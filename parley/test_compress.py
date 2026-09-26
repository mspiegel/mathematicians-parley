#!/usr/bin/env python3
"""Check that a compressed proof is the proof it was made from.

`parley/compress.py` rewrites a proof into the format set.mm is stored in,
and the whole of what makes that safe is that nothing about the proof
changes. A verifier is the other half of the answer and the gate runs one,
but a verifier says only that what it read is a proof; it cannot say that
what it read is the proof the elaborator built. This can, because the
format is reversible.

So every proof in the corpus is read back into the steps it was written
from and written out again, and the two compressed forms must be the same
text; one small enough to write out in normal format is read back as that
too. A round trip
through both directions catches an index written wrong, a saved step named
before it was kept, and a label block out of order — each of which could
otherwise leave a proof that verifies and is not the one that was meant.

Usage:  parley/test_compress.py [set.mm]
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from compress import (
    HIGH,
    LAST,
    compress,
    compressed,
    expand,
    expand_steps,
    letters,
    shapes,
    shapes_of,
)
from library import read as read_library
from library import where_set_mm
from spell import Builder

ROOT = Path(__file__).resolve().parent.parent
PROVED = re.compile(r'(?m)^\s*(\S+)\s+\$p\s+(.*?)\$=(.*?)\$\.', re.S)
STEPPED = 1_000_000          # labels, the most a proof is rebuilt as steps


def written_length(items):
    """How many labels the steps come to written out, counted without
    writing them: each step's length once, however often it is used.
    """
    length, work = {}, [(one, False) for one in items]
    while work:
        step, done = work.pop()
        if id(step) in length:
            continue
        if step.kids and not done:
            work.append((step, True))
            work.extend((kid, False) for kid in step.kids)
            continue
        length[id(step)] = 1 + sum(length[id(kid)] for kid in step.kids)
    return sum(length[id(one)] for one in items)


def decoded(said):
    """One index read the way `mmverify.py` reads it, to check `letters`."""
    running = 0
    for letter in said[:-1]:
        running = 5 * running + HIGH.index(letter) + 1
    return 20 * running + LAST.index(said[-1])


def main(argv):
    setmm = where_set_mm(argv)
    if setmm is None:
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2
    for index in [*range(4000), 10**5, 10**6]:
        if decoded(letters(index)) != index:
            print(f'  index {index} is written {letters(index)!r}, '
                  f'which reads back as {decoded(letters(index))}')
            return 1

    built = sorted((ROOT / 'elaboration').rglob('*.mm'))
    sigs = read_library(str(setmm), *(str(p) for p in built))
    spell = Builder(sigs)
    passed = failed = stepped = 0
    for path in built:
        for found in PROVED.finditer(path.read_text()):
            label, says, said = found.group(1), found.group(2), found.group(3)
            said = ' '.join(said.split())
            if not said.startswith('('):
                continue           # normal format, nothing to check
            # The same reckoning `parley/elaborate.py` makes when it writes
            # one. set.mm declares a float for `A` inside more than one
            # block, so which label a variable takes is `Builder`'s to say
            # and not something to work out again from the signatures.
            mandatory = sorted({spell.flabel[t] for t in says.split()
                                if t in spell.flabel},
                               key=lambda one: spell.forder[one])
            # Read back as the steps it was written from, which is how the
            # elaborator writes it, and written again from those.
            items = expand_steps(said, mandatory, sigs)
            again = compressed(*shapes_of(items), mandatory)
            if again == said:
                passed += 1
            else:
                failed += 1
                print(f'  NOT THE SAME  {label} in {path.name}')
            # And, where it is small enough to write out, read back as text
            # too: the two readings must number the proof alike. Written
            # out, the intermediate value proof is 467 million labels, and
            # reading those took two minutes of every gate.
            if written_length(items) < STEPPED:
                text = expand(said, mandatory, sigs)
                if compress(text, mandatory, sigs) == said \
                        and shapes_of(items) == shapes(text, sigs):
                    stepped += 1
                else:
                    failed += 1
                    print(f'  STEPS NUMBERED OTHERWISE  {label} in '
                          f'{path.name}')

    # A part of the wrong kind is refused where it is handed over: `eqid`
    # takes a class, and a proof is not one.
    try:
        spell.seq(spell.ap('0re'), 'eqid')
    except TypeError:
        refused = True
    else:
        refused = False
        failed += 1
        print('  a proof handed to eqid as a class was not refused')

    print(f'\n{passed} proof(s) survive a round trip, {failed} do not; '
          f'{stepped} numbered alike from their steps; a part of the wrong '
          f'kind {"is" if refused else "is not"} refused')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
