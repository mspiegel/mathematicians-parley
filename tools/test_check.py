#!/usr/bin/env python3
"""Check that the checker catches things.

Each case copies the corpus, makes one edit that should be a defect, and
requires that the reported problems change. A checker that passes a clean
corpus proves nothing on its own; this is the half that matters.

Usage:  tools/test_check.py
"""
import io
import shutil
import sys
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check                                            # noqa: E402

ROOT = Path(__file__).resolve().parent.parent

# The corpus is clean. A planted defect must therefore be reported, and the
# baseline run must report nothing.
BASELINE = 0

CASES = [
    ('cite a line inside a block that has closed',
     'proof/intermediate-value.proof',
     '    17.2.  c < b\n           inequalities, from 12, 17.1',
     '    17.2.  c < b\n           inequalities, from 12, 17.1.1',
     'inside a block that has closed'),

    ('cite a line that does not exist',
     'proof/sqrt2-irrational.proof',
     '    3.5.  p is even\n          thm:even-square n := p, from 3.1, 3.4',
     '    3.5.  p is even\n          thm:even-square n := p, from 3.1, 3.99',
     'does not exist'),

    ('cite the assumption of another case',
     'proof/triangle-inequality.proof',
     '    2.6.  −x ≤ |x|\n          inequalities, from 2.5',
     '    2.6.  −x ≤ |x|\n          inequalities, from 2.5, C1',
     'not in scope'),

    ('a justification that matches no production',
     'proof/sqrt2-irrational.proof',
     '3.  (2k + 1)² = 4k² + 4k + 1\n    algebra',
     '3.  (2k + 1)² = 4k² + 4k + 1\n    algebra from 1 and 2',
     'matches no production'),

    ('point at an item that is not in the database',
     'proof/cantor.proof',
     '    thm:set-builder-subset, from D1',
     '    thm:set-builder-nonesuch, from D1',
     'resolves to no item'),

    ('use def: for something that is a theorem',
     'proof/sqrt2-irrational.proof',
     '          requires n² ∈ ℤ: thm:int-closure, from H1',
     '          requires n² ∈ ℤ: def:int-closure, from H1',
     'names a theorem'),

    ('number a step under a parent that does not exist',
     'proof/cantor.proof',
     '2.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1',
     '2.9.4.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1',
     'does not exist'),

    ('use a part marker the method does not declare',
     'proof/triangle-inequality.proof',
     '    case\n    assume x ≥ 0',
     '    base\n    assume x ≥ 0',
     'is not one of the parts'),

    ('instantiate an item instead of a line',
     'proof/intermediate-value.proof',
     '    instantiate u := b in line 9, from H2, 7',
     '    instantiate u := b in def:least-upper-bound, from H2, 7',
     'never an item'),

    ('a character that is in no notation record',
     'proof/sum-formula.proof',
     '1.2.  1 = 1(1 + 1)/2',
     '1.2.  1 = 1(1 ⊕ 1)/2',
     'is in no record'),

    # U+2208 followed by a combining solidus looks like the not-an-element sign
    # and composes to it under NFC, so it is the decomposed form the rule bans.
    ('text that is not in Normalisation Form C',
     'proof/sqrt2-irrational.proof',
     '3.  √2 ∉ ℚ',
     '3.  √2 ∉ ℚ',
     'Normalisation Form C'),

    ('an item that says nothing about where it comes from',
     'db/items.db',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath    pw0',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}',
     'neither where it is proved'),

    ('a block whose method takes none',
     'proof/sum-formula.proof',
     '    1.2.  1 = 1(1 + 1)/2\n          arithmetic',
     '    1.2.  1 = 1(1 + 1)/2\n          arithmetic\n\n    1.2.1.  1 = 1\n            arithmetic',
     'takes no block'),

    ('a contradiction whose block does not suppose anything',
     'proof/sqrt2-irrational.proof',
     '    contradiction\n    suppose √2 ∈ ℚ                                                    (S)',
     '    contradiction',
     'does not open with `suppose`'),

    ('a theorem proved here and absent from the database',
     'proof/cantor.proof',
     'theorem cantor',
     'theorem cantor-two',
     'is in no record'),

    ('a let line that asserts instead of introducing',
     'proof/cantor.proof',
     '  let A be a set                                                      (H1)',
     '  let A ⊆ B                                                           (H1)',
     'none of the four introductions'),

    # Renaming the isosceles points to a and n makes the distance |an| spell
    # the declared word `an`, which is what the capital-letter convention has
    # been quietly preventing.
    ('two names run together into a declared word',
     'proof/isosceles.proof',
     '1.  |AC| = |CA|',
     '1.  |an| = |CA|',
     'run together'),

    # Line 4 of bezout binds s, so substituting a term naming s would capture.
    ('substitute a term that captures a bound variable',
     'proof/bezout.proof',
     '          instantiate s := a·x + b·y in line 4, from 7.1',
     '          instantiate s := a·x + b·s in line 4, from 7.1',
     'may not capture'),

    ('obtain a name without stating its sort',
     'proof/sqrt2-irrational.proof',
     '1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: def:odd n := n, from H1, H2',
     '1.  n = 2k + 1.\n    obtain k: def:odd n := n, from H1, H2',
     'without stating its sort'),

    ('write a claim in a notation nobody declared',
     'proof/infinitely-many-primes.proof',
     '6.  p > 1\n    def:prime p := p, from 5',
     '6.  p exceeds 1\n    def:prime p := p, from 5',
     'token(s) left over'),

    ('write a formula the sorts cannot read one way',
     'proof/subsets.proof',
     '1.2.1.5.  |T| = 2^k',
     '1.2.1.5.  |W| = 2^k',
     'the sorts do not separate them'),

    ('drop a line a citation needs for a hypothesis',
     'proof/intermediate-value.proof',
     '    def:interval x := a, from H1, H2',
     '    def:interval x := a, from H1',
     'does not supply them'),

    ('supply a hypothesis with the wrong number system',
     'proof/geometric-series.proof',
     '    2.1.  G(0) = 1\n          def:G, from H1',
     '    2.1.  G(0) = 1\n          def:G, from H3',
     'does not supply them'),

    ('stop declaring which pattern is a negation of which',
     'db/notation.db',
     '  level       predicate\n  negates     pattern 3 is logical-not of pattern 2',
     '  level       predicate',
     'does not supply them'),

    ('define a name and never say what it means',
     'proof/cantor.proof',
     '       reads the members of A that their own image leaves out\n',
     '',
     'carries no `reads` line'),

    ('note a step that opens no block',
     'proof/cantor.proof',
     '2.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1',
     '2.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1\n    note this is where B becomes a member',
     'opens no block'),

    ('suppose something unrelated to the claim',
     'proof/bezout.proof',
     '3.  r = 0\n    contradiction\n    suppose not r = 0',
     '3.  r = 0\n    contradiction\n    suppose not r ≤ 0',
     'neither expansion of `contradiction` applies'),

    ('end a contradiction block without a contradiction',
     'proof/infinitely-many-primes.proof',
     '    7.8.  p = 1. not p = 1.',
     '    7.8.  p = 1. p = 1.',
     'does not state a formula and that formula negated'),

    ('write a word predicate under a bare not',
     'db/items.db',
     '              not (P, Q, R are collinear)',
     '              not P, Q, R are collinear',
     'token(s) left over'),

    ('state an item in a notation nobody declared',
     'db/items.db',
     'theorem subset-transitive\n  assume X ⊆ Y',
     'theorem subset-transitive\n  assume X is within Y',
     'theorem subset-transitive'),

    ('leave the name in an item statement with no sort',
     'db/items.db',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P : X → formula                                                 (H2)',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)',
     'theorem set-builder-subset'),
]


def run(root):
    buf = io.StringIO()
    with redirect_stdout(buf):
        check.main(root)
    return buf.getvalue()


def main():
    passed = failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / 'clean'
        shutil.copytree(ROOT / 'db', clean / 'db')
        shutil.copytree(ROOT / 'proof', clean / 'proof')
        base = run(clean)
        n_base = int(base.split(' problem(s)')[0].split('\n')[-1])
        if n_base != BASELINE:
            print(f'baseline is {n_base} problem(s), expected {BASELINE}')
            print(base)
            return 1

        for name, rel, old, new, expect in CASES:
            work = Path(tmp) / 'work'
            shutil.rmtree(work, ignore_errors=True)
            shutil.copytree(clean, work)
            path = work / rel
            text = path.read_text(encoding='utf-8')
            if old not in text:
                print(f'  SETUP FAILED  {name}\n      anchor not found in {rel}')
                failed += 1
                continue
            path.write_text(text.replace(old, new, 1), encoding='utf-8')
            out = run(work)
            if expect in out:
                print(f'  caught        {name}')
                passed += 1
            else:
                print(f'  NOT CAUGHT    {name}')
                print(f'      expected a report containing {expect!r}')
                print('      got:', ' | '.join(
                    l for l in out.splitlines() if l and not l[0].isdigit())[:200])
                failed += 1

    print(f'\n{passed} caught, {failed} missed, of {len(CASES)} planted defects')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
