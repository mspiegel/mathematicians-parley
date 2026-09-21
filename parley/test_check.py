#!/usr/bin/env python3
"""Check that the checker catches things.

Each case copies the corpus, makes one edit that should be a defect, and
requires that the reported problems change. A checker that passes a clean
corpus proves nothing on its own; this is the half that matters.

Usage:  parley/test_check.py
"""
import io
import shutil
import sys
import tempfile
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check

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
     'db/items.records',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath    pw0',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}',
     'neither where it is proved'),

    ('a block whose method takes none',
     'proof/sum-formula.proof',
     '    1.2.  1 = 1(1 + 1)/2\n          arithmetic',
     ('    1.2.  1 = 1(1 + 1)/2\n          arithmetic\n\n'
      '    1.2.1.  1 = 1\n            arithmetic'),
     'takes no block'),

    ('a contradiction whose block does not suppose anything',
     'proof/sqrt2-irrational.proof',
     ('    contradiction\n    suppose √2 ∈ ℚ'
      '                                                    (S)'),
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
     'none of the five introductions'),

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
     '          instantiate s := a·x + b·y in line 5, from 10.2',
     '          instantiate s := a·x + b·s in line 5, from 10.2',
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
     'db/notation.records',
     '  level       predicate\n  negates     pattern 3 is logical-not of pattern 2',
     '  level       predicate',
     'does not supply them'),

    ('drop a hole from the term a notation builds',
     'db/notation.records',
     '  target      _1 _2 caddc co, _1 _2 cmin co',
     '  target      _1 _1 caddc co, _1 _2 cmin co',
     'leaves a hole out'),

    ('give a notation fewer targets than it has patterns',
     'db/notation.records',
     '  target      _1 _2 cmul co, _1 _2 cdiv co',
     '  target      _1 _2 cmul co',
     'target entr'),

    ('point a requires line at an item that does not cover it',
     'proof/sqrt2-irrational.proof',
     '    requires n² ∈ ℤ: thm:int-closure, from H1',
     '    requires n² ∈ ℤ: thm:int-real, from H1',
     'does not conclude'),

    ('drop the dull fact a requires line leans on',
     'proof/sqrt2-irrational.proof',
     '    requires 2 ∈ ℤ: arithmetic\n',
     '',
     'does not conclude'),

    ('claim something the cited item does not conclude',
     'proof/infinitely-many-primes.proof',
     '6.  p > 1\n    def:prime p := p, from 5',
     '6.  p > 2\n    def:prime p := p, from 5',
     'does not conclude'),

    # `G(n)` is the sum of the powers of `a`, and `def:G` fixes `a` for the
    # whole theorem rather than showing it in the notation. A proof that binds
    # an `a` of its own is writing about the name it bound.
    ('bind a name the notation it uses fixes',
     'proof/geometric-series.proof',
     '    2.9.  For every k ∈ ℕ₀, if G(k) = (1 − a^(k + 1))/(1 − a)\n'
     '          then G(k + 1) = (1 − a^((k + 1) + 1))/(1 − a).',
     '    2.9.  For every a ∈ ℕ₀, if G(a) = (1 − a^(a + 1))/(1 − a)\n'
     '          then G(a + 1) = (1 − a^((a + 1) + 1))/(1 − a).',
     'a proof may not bind a name the notation it uses fixes'),

    ('stop declaring that juxtaposition is the product',
     'db/notation.records',
     '  assoc       left\n  spells      multiplicative ·',
     '  assoc       left',
     'does not conclude'),

    ('stop saying which variable the braces bind',
     'db/items.records',
     '  then        u ∈ {t ∈ X : P(t)} ↔ u ∈ X and P(u)',
     '  then        t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t)',
     'does not conclude'),

    ('say a property is a function into a formula',
     'db/items.records',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P be a property of the elements of X                            (H2)',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P : X → formula                                                 (H2)',
     'which is a sort and not a set'),

    ('define a name and never say what it means',
     'proof/cantor.proof',
     '       reads the members of A that their own image leaves out\n',
     '',
     'carries no `reads` line'),

    ('note a step that opens no block',
     'proof/cantor.proof',
     '2.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1',
     ('2.  B ∈ 𝒫A\n    def:powerset S := B, from H1, 1\n'
      '    note this is where B becomes a member'),
     'opens no block'),

    ('suppose something unrelated to the claim',
     'proof/bezout.proof',
     '4.  r = 0\n    contradiction\n    suppose not r = 0',
     '4.  r = 0\n    contradiction\n    suppose not r ≤ 0',
     'neither expansion of `contradiction` applies'),

    ('end a contradiction block without a contradiction',
     'proof/infinitely-many-primes.proof',
     '    7.8.  p = 1. not p = 1.',
     '    7.8.  p = 1. p = 1.',
     'does not state a formula and that formula negated'),

    ('write a word predicate under a bare not',
     'db/items.records',
     '              not (P, Q, R are collinear)',
     '              not P, Q, R are collinear',
     'token(s) left over'),

    ('state an item in a notation nobody declared',
     'db/items.records',
     'theorem subset-transitive\n  assume X ⊆ Y',
     'theorem subset-transitive\n  assume X is within Y',
     'theorem subset-transitive'),

    ('leave the name in an item statement with no sort',
     'db/items.records',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P be a property of the elements of X                            (H2)',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)',
     'theorem set-builder-subset'),

    ('introduce a symbol and say nothing it stands for',
     'db/items.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr\n'
     '  then        x is irrational',
     'says nothing it stands for'),

    ('define a term and name no symbol for it',
     'db/items.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  defines     cr cq cdif\n'
     '  then        x is irrational',
     'names no symbol for it'),

    ('introduce a symbol nothing writes',
     'db/items.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr\n  defines     cr cq cdif\n'
     '  then        x is irrational',
     'cannot be reached'),

    ('introduce a symbol in more than one token',
     'db/items.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr ational\n'
     '  defines     cr cq cdif\n  then        x is irrational',
     'is not one token'),

    ('introduce one symbol from two definitions',
     'db/items.records',
     'definition irrational\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ',
     'definition irrational\n  symbol      dup\n  defines     cr\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ\n\n'
     'definition twice\n  symbol      dup\n  defines     cq\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ',
     'is already introduced by'),

    ('state a field twice, which reads as one field joined',
     'db/items.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  first-used  sqrt2-irrational\n'
     '  then        x is irrational',
     'a second time'),
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
                said = [x for x in out.splitlines() if x and not x[0].isdigit()]
                print('      got:', ' | '.join(said)[:200])
                failed += 1

    print(f'\n{passed} caught, {failed} missed, of {len(CASES)} planted defects')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
