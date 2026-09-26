#!/usr/bin/env python3
"""Generate `proved.mm`: what the library proves below the readable layer.

The corpus supplies an item in one of three ways: a set.mm label, a proof
file in the readable layer, or a Metamath proof here, for what set.mm does
not state and the readable layer cannot. Each group of them is a module of
its own (`proofs_geometry`, `proofs_series`), and each is written in a block
of its own, so
what one group holds apart (`$d`) holds nothing apart in another. A label is
global all the same, and a proof file that cites any of them includes this
one file.

This writes to standard output. Where the file goes is `parley/build.py`,
which is also what `parley/labels.py` and `parley/elaborate.py` ask, so the
three cannot drift apart. Run it through `parley/build.py stdlib/proved`
rather than redirecting by hand: written to the wrong place it is a file
nothing opens, and the build looks to have worked.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'parley'))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import proofs_geometry
import proofs_series
from build import path_of
from compress import compress
from library import Signature
from library import read as read_library
from spell import Builder

# The groups, in the order they are written: a later group may take a label
# an earlier one proved.
GROUPS = [proofs_geometry, proofs_series]

HEAD = """$( stdlib/proved, built by elaboration/stdlib/build-proved.py.

   What the library proves below the readable layer: facts this corpus
   needs, set.mm does not state, and the readable layer cannot. Each group
   stands in a block of its own. $)

$[ stdlib/definitions.mm $]

"""


def main(argv):
    if len(argv) < 2:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    # The angle is a constant this corpus introduces, so the definitions
    # are read alongside the library: `angval` says what a value of it is,
    # and discharging that needs `df-ang`.
    sigs = read_library(argv[1], path_of('stdlib/definitions'))
    b = Builder(sigs)
    made = {}
    print(HEAD, end='')
    for group in GROUPS:
        print('${')
        print(group.HEAD, end='')
        for label, statement, proof, *rest in group.proofs(b):
            # A lemma may state hypotheses (`$e`), as set.mm's deductions
            # do; they stand in a block of their own with it.
            hyps = rest[0] if rest else []
            if hyps:
                print('  ${')
                for said, stated in hyps:
                    print(f'    {said} $e {stated} $.')
            print(f'  {label} $p {statement} $=')
            # Compressed, as `parley/elaborate.py` writes its proofs. These
            # lemmas lean on each other, so a label written above is one a
            # proof below may take, and the library does not hold it; what
            # it takes is the variables of its statement and hypotheses,
            # then the hypotheses, which is what the signature records.
            words = ' '.join([statement, *(s for _l, s in hyps)]).split()
            floats = sorted({b.flabel[t] for t in words if t in b.flabel},
                            key=lambda one: b.forder[one])
            mandatory = floats + [said for said, _s in hyps]
            said = compress(proof.text, mandatory, {**sigs, **made})
            made[label] = Signature(label, '$p', statement.split(),
                                    [('class', v) for v in floats],
                                    [s.split() for _l, s in hyps])
            line = '   '
            for token in said.split():
                if len(line) + len(token) > 76:
                    print(line)
                    line = '   '
                line += ' ' + token
            print(f'{line} $.')
            if hyps:
                print('  $}')
            print()
        print('$}')
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
