#!/usr/bin/env python3
"""Check that the elaborator reports things rather than assuming them.

`test_check.py` does this for the checker, and the two are different
halves. The checker reads the text; the elaborator builds a proof from it,
and where it cannot it may take the step as stated instead — which is the
right answer for a method it does not expand, and the wrong one for a
defect somebody has to fix. Nothing was telling those apart until the two
exceptions were split, and nothing was testing that they stay apart.

Each case copies the corpus, makes one edit, and requires that elaborating
fails with a message naming where. A case that elaborates cleanly is the
failure this is looking for: the defect was swallowed.

Usage:  parley/test_elaborate.py [set.mm]
"""
import io
import shutil
import sys
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import elaborate
from library import where_set_mm
from parse import Problem, Unhandled

ROOT = Path(__file__).resolve().parent.parent

# Each: what it is, the theorem to elaborate, the file to edit, the text to
# find, what to put there, and what the message must contain. The expected
# text is part of the message rather than the whole of it, and includes the
# path where the point is that a defect says where it is.
CASES = [
    # `Elaborator.read` gave the parser no position, so a formula that did
    # not lex raised a defect carrying nowhere, which is what a route
    # declining carries. The step was assumed and the build went green.
    ('a requires line that does not lex',
     'geometric-sum', 'proof/geometric-series.proof',
     '                  requires a ∈ ℝ: from H1\n'
     '                  requires a^(k + 1) ∈ ℝ',
     '                  requires a ¿ ℝ: from H1\n'
     '                  requires a^(k + 1) ∈ ℝ',
     'proof/geometric-series.proof:65'),

    # `substitute` walks its equation both ways and each sentence of the
    # line it names, catching what declines. A name the proof never
    # introduced is not one of those, and used to be caught as one.
    ('substitute a name the proof never introduced',
     'geometric-sum', 'proof/geometric-series.proof',
     '          substitute a^(0 + 1) = a (line 2.5)',
     '          substitute a^(0 + 1) = z (line 2.5)',
     "no kernel name for 'z'"),

    # A gap in the database rather than in the text. It was reported with
    # no position at all, which read like a route declining.
    ('take away a target the corpus writes',
     'cantor', 'db/notation.records',
     '  target      _1 cpw',
     '  metamath    cpw-without-a-target',
     "notation 'powerset' has no target field"),

    # `decide_field` refuses a claim that is not an identity. It is raised
    # outside the handler that falls back to stating the step, and must
    # stay that way.
    ('claim an algebra step the cited lines do not give',
     'geometric-sum', 'proof/geometric-series.proof',
     '    2.9.5.  (1 − a^(k + 1))/(1 − a) + a^(k + 1) = '
     '(1 − a^(k + 1)·a)/(1 − a)',
     '    2.9.5.  (1 − a^(k + 1))/(1 − a) + a^(k + 1) = '
     '(1 − a^(k + 1)·a)/(1 − a) + 1',
     'is not an identity'),
]


def run(root, wanted, setmm):
    """What elaborating says, or None where it says nothing and builds."""
    buf = io.StringIO()
    try:
        with redirect_stdout(buf):
            elaborate.main(['elaborate.py', wanted, setmm], root)
    except Problem as said:
        return str(said)
    except Unhandled as said:
        return f'no method owns this step: {said}'
    return None


def main(argv):
    setmm = where_set_mm(argv)
    if setmm is None:
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2
    setmm = str(setmm)
    passed = failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / 'clean'
        for part in ('db', 'proof', 'parley', 'elaboration'):
            shutil.copytree(ROOT / part, clean / part,
                            ignore=shutil.ignore_patterns('__pycache__'))

        for name, wanted, rel, old, new, expect in CASES:
            # The corpus is clean, so the theorem must elaborate before the
            # edit. A case that fails here is testing nothing.
            if run(clean, wanted, setmm) is not None:
                print(f'  SETUP FAILED  {name}\n      {wanted} does not '
                      f'elaborate before the edit')
                failed += 1
                continue
            work = Path(tmp) / 'work'
            shutil.rmtree(work, ignore_errors=True)
            shutil.copytree(clean, work)
            path = work / rel
            text = path.read_text(encoding='utf-8')
            if old not in text:
                print(f'  SETUP FAILED  {name}\n      anchor not found in '
                      f'{rel}')
                failed += 1
                continue
            path.write_text(text.replace(old, new, 1), encoding='utf-8')
            said = run(work, wanted, setmm)
            if said is None:
                print(f'  NOT CAUGHT    {name}')
                print('      it elaborated: the defect was taken as stated')
                failed += 1
            elif expect in said:
                print(f'  caught        {name}')
                passed += 1
            else:
                print(f'  NOT CAUGHT    {name}')
                print(f'      expected {expect!r}')
                print(f'      got      {said[:160]!r}')
                failed += 1

    print(f'\n{passed} caught, {failed} missed, of {len(CASES)} planted '
          f'defects')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
