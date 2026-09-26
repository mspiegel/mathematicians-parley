#!/usr/bin/env python3
"""Check that the checker catches things.

Each case copies the corpus, makes one edit that should be a defect, and
requires that the reported problems change. A checker that passes a clean
corpus proves nothing on its own; this is the half that matters.

The cases run at once, each in a process of its own over a copy of its own,
so they share nothing but the machine; each checks the whole corpus, and one
after another they took over two minutes. What each found is printed in the
order the cases are listed.

Usage:  parley/test_check.py
"""
import io
import os
import shutil
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor
from contextlib import redirect_stdout
from itertools import repeat
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
     '    thm:stdlib/sets/set-builder-subset, from D1',
     '    thm:stdlib/sets/set-builder-nonesuch, from D1',
     'resolves to no item'),

    ('point at a library file that does not exist',
     'proof/cantor.proof',
     '    thm:stdlib/sets/set-builder-subset, from D1',
     '    thm:stdlib/nonesuch/set-builder-subset, from D1',
     'resolves to no item'),

    ('cite an item of another file by its bare name',
     'proof/cantor.proof',
     '    thm:stdlib/sets/set-builder-subset, from D1',
     '    thm:set-builder-subset, from D1',
     'names no theorem of this file'),

    ('use def: for something that is a theorem',
     'proof/sqrt2-irrational.proof',
     '          requires n² ∈ ℤ: thm:stdlib/numbers/int-closure, from H1',
     '          requires n² ∈ ℤ: def:stdlib/numbers/int-closure, from H1',
     'names a theorem'),

    ('number a step under a parent that does not exist',
     'proof/cantor.proof',
     '2.  B ∈ 𝒫A\n    def:stdlib/sets/powerset S := B, from 1',
     '2.9.4.  B ∈ 𝒫A\n    def:stdlib/sets/powerset S := B, from 1',
     'does not exist'),

    ('use a part marker the method does not declare',
     'proof/triangle-inequality.proof',
     '    case\n    assume x ≥ 0',
     '    base\n    assume x ≥ 0',
     'is not one of the parts'),

    ('instantiate an item instead of a line',
     'proof/intermediate-value.proof',
     '    instantiate u := b in line 9, from H2, 7',
     '    instantiate u := b in def:stdlib/calculus/least-upper-bound, from H2, 7',
     'never an item'),

    ('a character that is in no notation record',
     'proof/sum-formula.proof',
     '= 1(1 + 1)/2        arithmetic',
     '= 1(1 ⊕ 1)/2        arithmetic',
     'is in no record'),

    # U+2208 followed by a combining solidus looks like the not-an-element sign
    # and composes to it under NFC, so it is the decomposed form the rule bans.
    ('text that is not in Normalisation Form C',
     'proof/sqrt2-irrational.proof',
     '3.  √2 ∉ ℚ',
     '3.  √2 ∉ ℚ',
     'Normalisation Form C'),

    ('an item that says nothing about where it comes from',
     'stdlib/sets.records',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath    pw0',
     'theorem powerset-empty\n  then        𝒫∅ = {∅}',
     'neither which set.mm label'),

    ('a block whose method takes none',
     'proof/sum-formula.proof',
     '                  requires k ∈ ℝ: thm:stdlib/numbers/nat-real, from K\n',
     ('                  requires k ∈ ℝ: thm:stdlib/numbers/nat-real, from K\n\n'
      '                  1.3.3.1.  k = k\n'
      '                            algebra\n'),
     'takes no block'),

    ('a contradiction whose block does not suppose anything',
     'proof/sqrt2-irrational.proof',
     ('    contradiction\n    suppose √2 ∈ ℚ'
      '                                                    (S)'),
     '    contradiction',
     'does not open with `suppose`'),

    ('cite another proof file without importing it',
     'proof/intermediate-value.proof',
     'import proof/triangle-inequality\n',
     '',
     'proof/triangle-inequality is not imported'),

    ('import a proof file and cite nothing from it',
     'proof/cantor.proof',
     'theorem cantor\n',
     'import proof/bezout\n\ntheorem cantor\n',
     'imports proof/bezout and cites nothing from it'),

    ('import the standard library',
     'proof/cantor.proof',
     'theorem cantor\n',
     'import stdlib/sets\n\ntheorem cantor\n',
     'the standard library is never imported'),

    ('import a file that is not there',
     'proof/cantor.proof',
     'theorem cantor\n',
     'import proof/nonesuch\n\ntheorem cantor\n',
     'import proof/nonesuch names no proof file'),

    ('import the same file twice',
     'proof/intermediate-value.proof',
     'import proof/triangle-inequality\n',
     'import proof/triangle-inequality\nimport proof/triangle-inequality\n',
     'proof/triangle-inequality is imported twice'),

    ('a proof file that imports itself',
     'proof/cantor.proof',
     'theorem cantor\n',
     'import proof/cantor\n\ntheorem cantor\n',
     'proof/cantor imports itself'),

    ('two proof files that import each other',
     'proof/triangle-inequality.proof',
     'theorem abs-bounds\n',
     'import proof/intermediate-value\n\ntheorem abs-bounds\n',
     'closes a cycle'),

    ('two theorems of one name in one file',
     'proof/sqrt2-irrational.proof',
     'theorem even-square\n',
     'theorem odd-square\n',
     'theorem odd-square is already proved'),

    ('two items of one name in one library file',
     'stdlib/sets.records',
     'theorem powerset-empty\n',
     'theorem powerset-monotone\n',
     'theorem powerset-monotone is already defined'),

    ('an item stated outside the standard library',
     'db/methods.records',
     'method algebra\n',
     'theorem stray\n  then        P\n  metamath    exmid\n\nmethod algebra\n',
     'stray is outside stdlib/'),

    ('a theorem field said twice',
     'proof/cantor.proof',
     '  metamath    canth\n',
     '  metamath    canth\n  metamath    canth\n',
     'says metamath twice'),

    ('a let line that asserts instead of introducing',
     'proof/cantor.proof',
     '  let A be a set                                                      (H1)',
     '  let A ⊆ B                                                           (H1)',
     'none of the 7 introductions'),

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
     '1.  k ∈ ℤ. n = 2k + 1.\n'
     '    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2',
     '1.  n = 2k + 1.\n    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2',
     'without stating its sort'),

    ('write a claim in a notation nobody declared',
     'proof/infinitely-many-primes.proof',
     '6.  p > 1\n    def:stdlib/divisibility/prime p := p, from 5',
     '6.  p exceeds 1\n    def:stdlib/divisibility/prime p := p, from 5',
     'token(s) left over'),

    ('write a formula the sorts cannot read one way',
     'proof/subsets.proof',
     '1.2.1.5.  |T| = 2^k',
     '1.2.1.5.  |W| = 2^k',
     'the sorts do not separate them'),

    ('drop a line a citation needs for a hypothesis',
     'proof/intermediate-value.proof',
     '    def:stdlib/calculus/interval x := a, from H1, H2',
     '    def:stdlib/calculus/interval x := a, from H1',
     'does not supply them'),

    ('supply a hypothesis with the wrong number system',
     'proof/geometric-series.proof',
     '    2.1.  G(0) = 1\n          def:stdlib/sums/G, from H1',
     '    2.1.  G(0) = 1\n          def:stdlib/sums/G, from H3',
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
     '    requires n² ∈ ℤ: thm:stdlib/numbers/int-closure, from H1',
     '    requires n² ∈ ℤ: thm:stdlib/numbers/int-real, from H1',
     'does not conclude'),

    ('drop the dull fact a requires line leans on',
     'proof/sqrt2-irrational.proof',
     '    requires 2 ∈ ℤ: arithmetic\n',
     '',
     'does not conclude'),

    ('claim something the cited item does not conclude',
     'proof/infinitely-many-primes.proof',
     '6.  p > 1\n    def:stdlib/divisibility/prime p := p, from 5',
     '6.  p > 2\n    def:stdlib/divisibility/prime p := p, from 5',
     'does not conclude'),

    # `G(n)` is the sum of the powers of `a`, and `def:stdlib/sums/G` fixes `a`
    # for the whole theorem rather than showing it in the notation. A proof
    # that binds an `a` of its own is writing about the name it bound.
    ('bind a name the notation it uses fixes',
     'proof/geometric-series.proof',
     '    2.8.  For every k ∈ ℕ₀, if G(k) = (1 − a^(k + 1))/(1 − a)\n'
     '          then G(k + 1) = (1 − a^((k + 1) + 1))/(1 − a).',
     '    2.8.  For every a ∈ ℕ₀, if G(a) = (1 − a^(a + 1))/(1 − a)\n'
     '          then G(a + 1) = (1 − a^((a + 1) + 1))/(1 − a).',
     'a proof may not bind a name the notation it uses fixes'),

    # The same fixed name is said twice and neither file reads the other:
    # `def:stdlib/sums/G`'s `let` lines and the hole of `G(_)` say it on the
    # page, and `@a` in the target says it to the elaborator.
    ('drop the fixed parameter from a notation target',
     'db/notation.records',
     '  target      cc0 _1 cfz co @a vk cv cexp co vk csu',
     '  target      cc0 _1 cfz co c1 vk cv cexp co vk csu',
     'which its target does not write as @a'),

    ('hold a name fixed that no definition fixes',
     'db/notation.records',
     '  target      cc0 _1 cfz co @a vk cv cexp co vk csu',
     '  target      cc0 _1 cfz co @a @b vk cv cexp co vk csu',
     'which no definition introducing it fixes'),

    ('stop declaring that juxtaposition is the product',
     'db/notation.records',
     '  assoc       left\n  spells      multiplicative ·',
     '  assoc       left',
     'does not conclude'),

    ('stop saying which variable the braces bind',
     'stdlib/sets.records',
     '  then        u ∈ {t ∈ X : P(t)} ↔ u ∈ X and P(u)',
     '  then        t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t)',
     'does not conclude'),

    ('say a property is a function into a formula',
     'stdlib/sets.records',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P be a property of the elements of X                            (H2)',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P : X → formula                                                 (H2)',
     'which is a sort and not a set'),

    # A define with an argument is a function, and a function is defined
    # somewhere: its rule alone says what it does and not where.
    ('define a function and give no domain',
     'proof/cantor.proof',
     'define B := {x ∈ A : x ∉ f(x)}',
     'define B(y) := {x ∈ A : x ∉ f(x)}',
     'says no domain'),

    ('give a domain to a define that takes no argument',
     'proof/cantor.proof',
     'define B := {x ∈ A : x ∉ f(x)}',
     'define B := {x ∈ A : x ∉ f(x)}, for y ∈ A',
     'gives a domain and takes no argument'),

    ('define a name and never say what it means',
     'proof/cantor.proof',
     '       reads the members of A that their own image leaves out\n',
     '',
     'carries no `reads` line'),

    ('note a step that opens no block',
     'proof/cantor.proof',
     '2.  B ∈ 𝒫A\n    def:stdlib/sets/powerset S := B, from 1',
     ('2.  B ∈ 𝒫A\n    def:stdlib/sets/powerset S := B, from 1\n'
      '    note this is where B becomes a member'),
     'opens no block'),

    # An item's summand is whatever the sum it concludes sums, read where the
    # sum applies it to what it binds, and every other use of it must agree.
    ('sum over a range the item does not conclude',
     'proof/divisibility-by-three.proof',
     '2.  3 divides Σ(k = 0 to n) (d(k)·10^k − d(k))',
     '2.  3 divides Σ(k = 1 to n) (d(k)·10^k − d(k))',
     'step 2 claims something that thm:stdlib/sums/sum-divisible does not '
     'conclude'),

    ('read an item\'s summand two ways',
     'proof/divisibility-by-three.proof',
     '= Σ(k = 0 to n) d(k)·10^k − Σ(k = 0 to n) d(k)\n'
     '    thm:stdlib/sums/sum-difference',
     '= Σ(k = 0 to n) d(k) − Σ(k = 0 to n) d(k)\n'
     '    thm:stdlib/sums/sum-difference',
     'step 3 claims something that thm:stdlib/sums/sum-difference does not '
     'conclude'),

    # A congruence is a divisibility of a difference, and which way round
    # the difference goes is part of what is said.
    ('turn a congruence round',
     'proof/divisibility-by-three.proof',
     '    1.1.  10^k ≡ 1 (mod 3)\n          thm:ten-power-congruent',
     '    1.1.  1 ≡ 10^k (mod 3)\n          thm:ten-power-congruent',
     'step 1.1 claims something that thm:ten-power-congruent does not '
     'conclude'),

    ('note a case part after its assumption',
     'proof/subsets.proof',
     ('          note V is a subset without a, with a put back\n'
      '          assume a ∈ V                                                (C1)'),
     ('          assume a ∈ V                                                (C1)\n'
      '          note V is a subset without a, with a put back'),
     'directly under its marker'),

    ('note a case part twice',
     'proof/subsets.proof',
     '          note V is a subset without a, with a put back\n',
     ('          note V is a subset without a, with a put back\n'
      '          note V holds a\n'),
     'already carries a note'),

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
     'stdlib/geometry.records',
     '              not (P, Q, R are collinear)',
     '              not P, Q, R are collinear',
     'token(s) left over'),

    ('state an item in a notation nobody declared',
     'stdlib/sets.records',
     'theorem subset-transitive\n  assume X ⊆ Y',
     'theorem subset-transitive\n  assume X is within Y',
     'theorem subset-transitive'),

    ('leave the name in an item statement with no sort',
     'stdlib/sets.records',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)\n'
     '  let P be a property of the elements of X                            (H2)',
     'theorem set-builder-subset\n  let X be a set'
     '                                                      (H1)',
     'theorem set-builder-subset'),

    ('introduce a symbol and say nothing it stands for',
     'stdlib/numbers.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr\n'
     '  then        x is irrational',
     'says nothing it stands for'),

    ('define a term and name no symbol for it',
     'stdlib/numbers.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  defines     cr cq cdif\n'
     '  then        x is irrational',
     'names no symbol for it'),

    ('introduce a symbol nothing writes',
     'stdlib/numbers.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr\n  defines     cr cq cdif\n'
     '  then        x is irrational',
     'cannot be reached'),

    ('introduce a symbol in more than one token',
     'stdlib/numbers.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  symbol      irr ational\n'
     '  defines     cr cq cdif\n  then        x is irrational',
     'is not one token'),

    ('introduce one symbol from two definitions',
     'stdlib/numbers.records',
     'definition irrational\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ',
     'definition irrational\n  symbol      dup\n  defines     cr\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ\n\n'
     'definition twice\n  symbol      dup\n  defines     cq\n'
     '  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ',
     'is already introduced by'),

    ('state a field twice, which reads as one field joined',
     'stdlib/numbers.records',
     'definition irrational\n  then        x is irrational',
     'definition irrational\n  first-used  sqrt2-irrational\n'
     '  then        x is irrational',
     'a second time'),

    # Everything a citation names does work. Line 1 says a + b ∈ ℝ, which
    # is what `thm:stdlib/numbers/nonneg-or-neg` asks; H1 says a ∈ ℝ, which
    # it does not.
    ('cite a line the cited item asks nothing of',
     'proof/triangle-inequality.proof',
     '    thm:stdlib/numbers/nonneg-or-neg x := a + b, from 1\n',
     '    thm:stdlib/numbers/nonneg-or-neg x := a + b, from 1, H1\n',
     'step 2 cites H1, and thm:stdlib/numbers/nonneg-or-neg asks for nothing '
     'it says'),

    # A "there is" given by an instance is given only where the instance is
    # in the domain. Bezout's step 2 puts a in S by exhibiting 1 and 0, and
    # without `requires 1 ∈ ℤ` the 1 could be anything.
    ('exhibit a witness without saying it is in the domain',
     'proof/bezout.proof',
     '    def:stdlib/sets/set-builder u := a, from H1, 1\n'
     '    requires 1 ∈ ℤ: arithmetic\n',
     '    def:stdlib/sets/set-builder u := a, from H1, 1\n',
     'step 2 claims something that def:stdlib/sets/set-builder does not '
     'conclude'),

    # A sort is stated once, like a declared type, and a step does not cite
    # it to rely on it (`READERS.md`): citing one names a line that does no
    # work.
    ('cite the line that says what kind of thing a name is',
     'proof/isosceles.proof',
     '    thm:stdlib/geometry/distance-symmetric P := A, Q := C\n',
     '    thm:stdlib/geometry/distance-symmetric P := A, Q := C, from H1\n',
     'step 1 cites H1, and thm:stdlib/geometry/distance-symmetric asks for '
     'nothing it says'),

    # An obtain names its item after the word `obtain`, and the checks that
    # read an item citation read only a step the item heads. The three
    # below went unreported.
    ('obtain from an item without what it asks for',
     'proof/intermediate-value.proof',
     '    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7',
     '    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 7',
     'step 8 cites thm:stdlib/calculus/completeness, which asks for'),

    ('obtain from an item and cite a line it does not ask for',
     'proof/intermediate-value.proof',
     '    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7',
     '    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7, H3',
     'step 8 cites H3, and thm:stdlib/calculus/completeness asks for nothing '
     'it says'),

    # An item with no target is assumed as it states itself. This one said
    # |X| = k + 1 without saying what k was, and at k = −1 and X = ∅ the
    # axiom it became was false.
    ('leave open a name an item uses as a number',
     'stdlib/counting.records',
     'theorem card-nonempty\n'
     '  let X be a set                                                      (H1)\n'
     '  let k ∈ ℕ₀                                                          (H2)\n',
     'theorem card-nonempty\n'
     '  let X be a set                                                      (H1)\n',
     'theorem card-nonempty: k stands where a number goes'),

    # A set has the kind of what it holds, and the page never writes it
    # (`READERS.md`); the checker reads it off the text. Flat sorts saw none
    # of the three below: to them a set was a set.
    ('put a set of numbers inside a set of sets of numbers',
     'proof/intermediate-value.proof',
     '3.  S ⊆ [a, b]\n',
     '3.  S ⊆ 𝒫[a, b]\n',
     '𝒫: a set of sets of numbers where a set of numbers is wanted'),

    ('say an element of a set of numbers is a set',
     'proof/intermediate-value.proof',
     '    6.1.  s ∈ [a, b]\n          def:stdlib/sets/set-builder, from K1\n',
     '    6.1.  s ∈ [a, b]\n          def:stdlib/sets/set-builder, from K1\n'
     '          requires s is a set: from K1\n',
     's: a number where a set of things of a kind not yet fixed is wanted'),

    # A set declared of any kind stays any kind. `let a be a set` made
    # add-element-bijection's X a set of sets, and subsets-count, whose X is
    # a set of any kind, cited it: the counting proof would hold of sets of
    # sets only, and nothing said so.
    ('cite a statement that narrows a set of any kind',
     'proof/subsets.proof',
     '  let a ∉ X                                                           (H2)\n',
     '  let a ∉ X                                                           (H2)\n'
     '  let a be a set                                                      (H3)\n',
     'citing proof/subsets/add-element-bijection with X := X ∖ {a}: a set of '
     'things of any kind (X)'),

    ('obtain from a definition without the line it unfolds',
     'proof/sqrt2-irrational.proof',
     '    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2',
     '    obtain k: def:stdlib/divisibility/odd n := n, from H1',
     'step 1 obtains from def:stdlib/divisibility/odd, which says there is one '
     'only from'),

    # Pascal's rule pairs C(n, k) with C(n, k − 1). The other neighbour is
    # the mistake a reader makes when the index shift goes the wrong way.
    ('Pascal with the shift going the wrong way',
     'proof/binomial.proof',
     '    47.5.  C(m, k) + C(m, k − 1) = C(m + 1, k)\n',
     '    47.5.  C(m, k) + C(m, k + 1) = C(m + 1, k)\n',
     'step 47.5 claims something that thm:stdlib/counting/pascal does not '
     'conclude'),

    # Shifting the index moves the range with it.
    ('a shifted sum left over the range it came from',
     'proof/binomial.proof',
     '27. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 + 1 to m + 1)',
     '27. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 to m)',
     'step 27 claims something that thm:stdlib/sums/sum-shift does not '
     'conclude'),

    # A line saying something of every index from 0 to m says nothing of
    # the index m + 1, which the sum to m + 1 takes.
    ('a term-by-term line over too short a range',
     'proof/binomial.proof',
     '    thm:stdlib/sums/sum-termwise a := 0, b := m + 1, from 47\n',
     '    thm:stdlib/sums/sum-termwise a := 0, b := m + 1, from 8\n',
     'step 48 cites thm:stdlib/sums/sum-termwise, which asks for'),

    # C(n, k) is zero above n, and C(m + 1, m + 1) is not above it.
    ('a coefficient called zero where k is not above n',
     'proof/binomial.proof',
     '    thm:stdlib/counting/binomial-above n := m, k := m + 1, from H3, 3, 10',
     '    thm:stdlib/counting/binomial-above n := m + 1, k := m + 1, '
     'from H3, 3, 10',
     'step 11 cites thm:stdlib/counting/binomial-above, which asks for'),

    # Four blocks of binomial-step each fix k under the label J, and J means
    # what the block around the citing step says: here k runs from 1. Read
    # theorem-wide, J was the last block's, from 0, and this edit passed.
    ('a label read as a sibling block\'s',
     'proof/binomial.proof',
     'thm:stdlib/sums/range-integer a := 1, b := m + 1, from J\n'
     '           requires 1 ∈ ℤ: arithmetic\n',
     'thm:stdlib/sums/range-integer a := 0, b := m + 1, from J\n'
     '           requires 0 ∈ ℤ: arithmetic\n',
     'step 29.1 cites thm:stdlib/sums/range-integer, which asks for'),

    # `arithmetic` may stand where a closed-numeral fact is used, and only
    # there: an equation with a letter in it gives a reader something to
    # check, and is a numbered step. `SYNTAX.md` has the rule.
    ('take an equation with a letter in it from arithmetic',
     'proof/binomial.proof',
     'substitute (m + 1) − 0 = m + 1 (line 34)',
     'substitute (m + 1) − 0 = m + 1 (arithmetic)',
     'takes (m + 1) − 0 = m + 1 from arithmetic, and it has a letter in it'),

    ('a chain link with a letter in it naming arithmetic',
     'proof/sum-formula.proof',
     '= (k + 1)((k + 1) + 1)/2       1.3.3',
     '= (k + 1)((k + 1) + 1)/2       arithmetic',
     'names arithmetic for'),

    # What a summand's function hypothesis asks is the membership of the
    # names the summand is built from, and 1 is none of them.
    ('a requires line the summand does not ask for',
     'proof/binomial.proof',
     '    thm:stdlib/sums/sum-real a := 0, b := m\n'
     '    requires 0 ∈ ℤ: arithmetic\n',
     '    thm:stdlib/sums/sum-real a := 0, b := m\n'
     '    requires 1 ∈ ℤ: arithmetic\n'
     '    requires 0 ∈ ℤ: arithmetic\n',
     'says 1 ∈ ℤ, and neither thm:stdlib/sums/sum-real nor'),
]


def run(root):
    buf = io.StringIO()
    with redirect_stdout(buf):
        check.main(root)
    return buf.getvalue()


def plant(case, clean, work):
    """Plant one case's defect in a copy of its own and check it.

    Gives back whether it was caught and what to say about it.
    """
    name, rel, old, new, expect = case
    shutil.copytree(clean, work)
    path = work / rel
    text = path.read_text(encoding='utf-8')
    if old not in text:
        return False, f'  SETUP FAILED  {name}\n      anchor not found in {rel}'
    path.write_text(text.replace(old, new, 1), encoding='utf-8')
    out = run(work)
    if expect in out:
        return True, f'  caught        {name}'
    said = [x for x in out.splitlines() if x and not x[0].isdigit()]
    return False, (f'  NOT CAUGHT    {name}\n'
                   f'      expected a report containing {expect!r}\n'
                   f'      got: {" | ".join(said)[:200]}')


def main():
    with tempfile.TemporaryDirectory() as tmp:
        clean = Path(tmp) / 'clean'
        for part in ('db', 'stdlib', 'proof'):
            shutil.copytree(ROOT / part, clean / part)
        base = run(clean)
        n_base = int(base.split(' problem(s)')[0].split('\n')[-1])
        if n_base != BASELINE:
            print(f'baseline is {n_base} problem(s), expected {BASELINE}')
            print(base)
            return 1

        works = [Path(tmp) / f'work-{i}' for i in range(len(CASES))]
        with ProcessPoolExecutor(max_workers=os.cpu_count() or 1) as pool:
            results = list(pool.map(plant, CASES, repeat(clean), works))

    for _caught, said in results:
        print(said)
    passed = sum(caught for caught, _said in results)
    failed = len(results) - passed
    print(f'\n{passed} caught, {failed} missed, of {len(CASES)} planted defects')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
