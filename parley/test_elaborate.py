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
from parse import Problem

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

    # A database defect rather than a text one, and on an item rather than
    # a notation: the target names a lemma that proves the other `then`
    # group, so the step's own group has nothing behind it.
    ('name the wrong clause in a definition target',
     'geometric-sum', 'db/items.records',
     '  target      fsum1, fsump1\n'
     '  first-used  geometric-series',
     '  target      fsum1, fsum1\n'
     '  first-used  geometric-series',
     'proof/geometric-series.proof:53  no clause of def:G gives what '
     'step 2.9.1 claims'),

    # The same report reached from the other side: the target is right and
    # the step claims something the definition does not say. It used to be
    # given back as a route declining, which anything above was free to
    # take as stated.
    ('claim of a definition what it does not say',
     'geometric-sum', 'proof/geometric-series.proof',
     '    2.1.  G(0) = 1',
     '    2.1.  G(0) = 2',
     'proof/geometric-series.proof:15  no clause of def:G gives what '
     'step 2.1 claims'),

    # A `requires` line has a claim and a reason, and only the claim was
    # used: the reason could name any line at all and the fact was settled
    # from whatever the scope held. Here line 6 does not say `C ≠ A` and
    # line 7 does, and the proof took it from the theorem's own hypothesis
    # and turned it with `necom`, so the file verified and the line the
    # page named went unused.
    ('name a line that does not state the side condition',
     'isosceles', 'proof/isosceles.proof',
     '    requires C ≠ A: def:triangle, from 7',
     '    requires C ≠ A: def:triangle, from 6',
     'proof/isosceles.proof:43  def:triangle, from 6 does not reach'),

    # The same, where the scope already holds the claim for another reason:
    # the hypothesis says A, B, C form a triangle, so `A ≠ B` is held before
    # the line is read, and line 7 does not say it.
    ('name a line that does not state a claim the scope already holds',
     'isosceles', 'proof/isosceles.proof',
     '    requires A ≠ B: def:triangle, from 6',
     '    requires A ≠ B: def:triangle, from 7',
     'proof/isosceles.proof:48  def:triangle, from 7 does not reach'),

    # A step's proof rests only on what it names (`GOALS.md` decision 9).
    # Without its requires line, `algebra` wants k ∈ ℂ, and the scope holds
    # k ∈ ℤ from line 1, which step 3 does not cite. Offered that, the step
    # elaborated and verified; it is not offered, so nothing says k ∈ ℂ.
    ('lean on a line the step does not name',
     'odd-square', 'proof/sqrt2-irrational.proof',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: thm:int-real, from 1\n',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n',
     'proof/sqrt2-irrational.proof:12  nothing says m e. CC, which this '
     'step needs'),

    # A requires line rests only on its reason. Line 2 does not say k is an
    # integer, and `thm:int-real` asks it; the scope has it from line 1,
    # which the line does not cite, so the item it names reaches nothing.
    ('give a requires line a reason that is not where its proof comes from',
     'odd-square', 'proof/sqrt2-irrational.proof',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: thm:int-real, from 1\n',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: thm:int-real, from 2\n',
     'proof/sqrt2-irrational.proof:12  thm:int-real targets zre, and none '
     'of them reaches m e. RR'),

    # Everything a step names does work. 2 is a numeral, not an atom, so
    # `algebra` asks nothing about its being real, and the kernel has it
    # from the library; the line is true, well formed, and does nothing.
    ('write a requires line nothing asks for',
     'sum-formula', 'proof/sum-formula.proof',
     '                  requires 2 ≠ 0: arithmetic\n',
     '                  requires 2 ≠ 0: arithmetic\n'
     '                  requires 2 ∈ ℝ: arithmetic\n',
     'says 2 ∈ ℝ, and the step neither uses nor asks for it'),

    # The certificate combines lines 3 and 4; line 1 says a + b ∈ ℝ, which
    # the step writes as its atoms instead, and is cited for nothing.
    ('cite a line a method step does not combine',
     'triangle-inequality', 'proof/triangle-inequality.proof',
     '    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 3, 4\n',
     '    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 1, 3, 4\n',
     'step 5.2 cites 1 and uses nothing it says'),

    # Each atom a method combines is real, and the step says so. The
    # kernel's `ltne` never needs d ∈ ℝ here, so nothing else would see the
    # line gone: only what the method asks for does.
    ('leave out the membership of an atom the method combines',
     'lowest-terms', 'proof/sqrt2-irrational.proof',
     '    5.7.  d ≠ 1\n          inequalities, from 5.1\n'
     '          requires d ∈ ℝ: thm:int-real, from 5.1\n',
     '    5.7.  d ≠ 1\n          inequalities, from 5.1\n',
     'step 5.7 combines d, and nothing it writes or cites says it is a '
     'number'),

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

    # A side condition is searched for among what the step names, not among
    # everything in scope. Without 1.2.1.5 the step still needs T finite,
    # and the scope holds |T| = 2^k: offered it, the search found the route
    # and R1 refused it afterwards, so which route the search took decided
    # whether a correct page was reported. It must not be offered at all.
    ('settle a side condition from a line the step does not cite',
     'subsets-count', 'proof/subsets.proof',
     'n := 2^k, from 1.2.1.3, 1.2.1.5, 1.2.1.6',
     'n := 2^k, from 1.2.1.3, 1.2.1.6',
     'no clause of thm:card-disjoint-union reaches what step 1.2.1.8 '
     'claims'),

    # An item taken as stated is stated as the item says it. Stating the
    # step's claim under the item's hypotheses instead assumed whatever the
    # step claimed, and the kernel accepts whatever is assumed.
    ('claim what an item taken as stated does not state',
     'subsets-count', 'proof/subsets.proof',
     '                  1.2.1.7.  𝒫X = U ∪ T\n',
     '                  1.2.1.7.  𝒫X = U\n',
     'thm:powerset-split is taken as stated and states'),

    # An item's target asks a side condition the page never writes, and
    # `rewritten` answers it through the equation the step cites: `0 < |X|`
    # is `0 < k + 1` by C2. Without C2 cited, the equation is in scope and
    # not in hand, and the side condition must go unanswered.
    ('answer a side condition by an equation the step does not cite',
     'subsets-count', 'proof/subsets.proof',
     'obtain a: thm:card-nonempty, from K2, C2',
     'obtain a: thm:card-nonempty, from K2',
     'thm:card-nonempty targets hashgt0elex, and none of them reaches'),

    # A target is where the claim lands, and a variable bound to the wrong
    # name makes it land somewhere else. That is reported, not assumed.
    ('bind a target variable to the wrong name',
     'subsets-count', 'db/items.records',
     '  target      hashdifsnp1 with V := X, N := a, Y := k',
     '  target      hashdifsnp1 with V := X, N := a, Y := X',
     'no clause of thm:card-remove reaches what step 1.2.1.2 claims'),
]


def run(root, wanted, setmm):
    """What elaborating says, or None where it says nothing and builds."""
    buf = io.StringIO()
    try:
        with redirect_stdout(buf):
            elaborate.main(['elaborate.py', wanted, setmm], root)
    except Problem as said:
        return str(said)
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

        # The corpus is clean, so the theorem must elaborate before the
        # edit. A case that fails here is testing nothing. Asked once per
        # theorem rather than once per case: the corpus is the same corpus
        # each time, and five of these cases are about one theorem that
        # takes ten seconds to elaborate.
        healthy = {}
        for name, wanted, rel, old, new, expect in CASES:
            if wanted not in healthy:
                healthy[wanted] = run(clean, wanted, setmm)
            if healthy[wanted] is not None:
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
