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
import contextlib
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
     'proof/geometric-series/geometric-sum',
     'proof/geometric-series.proof',
     '                  requires a ∈ ℝ: from H1\n'
     '                  requires a^(k + 1) ∈ ℝ',
     '                  requires a ¿ ℝ: from H1\n'
     '                  requires a^(k + 1) ∈ ℝ',
     'proof/geometric-series.proof:86'),

    # `substitute` walks its equation both ways and each sentence of the
    # line it names, catching what declines. A name the proof never
    # introduced is not one of those, and used to be caught as one.
    ('substitute a name the proof never introduced',
     'proof/geometric-series/geometric-sum',
     'proof/geometric-series.proof',
     '          substitute a^(0 + 1) = a (line 2.6)',
     '          substitute a^(0 + 1) = z (line 2.6)',
     "no kernel name for 'z'"),

    # A gap in the database rather than in the text. It was reported with
    # no position at all, which read like a route declining.
    ('take away a target the corpus writes',
     'proof/cantor/cantor',
     'db/notation.records',
     '  target      _1 cpw',
     '  metamath    cpw-without-a-target',
     "notation 'powerset' has no target field"),

    # A database defect rather than a text one, and on an item rather than
    # a notation: the target names a lemma that proves the other `then`
    # group, so the step's own group has nothing behind it.
    ('name the wrong clause in a definition target',
     'proof/triangle-inequality/abs-bounds',
     'stdlib/numbers.records',
     '  target      absid, absnid\n',
     '  target      absid, absid\n',
     'proof/triangle-inequality.proof:34  no clause of '
     'def:stdlib/numbers/abs gives what step 2.5 claims'),

    # The same report reached from the other side: the target is right and
    # the step claims something the definition does not say. It used to be
    # given back as a route declining, which anything above was free to
    # take as stated.
    ('claim of a definition what it does not say',
     'proof/triangle-inequality/abs-bounds',
     'proof/triangle-inequality.proof',
     '    2.5.  |x| = −x',
     '    2.5.  |x| = x',
     'proof/triangle-inequality.proof:34  no clause of '
     'def:stdlib/numbers/abs gives what step 2.5 claims'),

    # A `requires` line has a claim and a reason, and only the claim was
    # used: the reason could name any line at all and the fact was settled
    # from whatever the scope held. Here line 5 does not say `C ≠ A` and
    # line 6 does, and the proof took it from the theorem's own hypothesis
    # and turned it with `necom`, so the file verified and the line the
    # page named went unused.
    ('name a line that does not state the side condition',
     'proof/isosceles/isosceles',
     'proof/isosceles.proof',
     '    requires C ≠ A: def:stdlib/geometry/triangle, from 6',
     '    requires C ≠ A: def:stdlib/geometry/triangle, from 5',
     'def:stdlib/geometry/triangle, from 5 does not reach'),

    # The same, where the scope already holds the claim for another reason:
    # the hypothesis says A, B, C form a triangle, so `A ≠ B` is held before
    # the line is read, and line 6 does not say it.
    ('name a line that does not state a claim the scope already holds',
     'proof/isosceles/isosceles',
     'proof/isosceles.proof',
     '    requires A ≠ B: def:stdlib/geometry/triangle, from 5',
     '    requires A ≠ B: def:stdlib/geometry/triangle, from 6',
     'def:stdlib/geometry/triangle, from 6 does not reach'),

    # A step's proof rests only on what it names (`GOALS.md` decision 9).
    # Without its requires line, `algebra` wants k ∈ ℂ, and the scope holds
    # k ∈ ℤ from line 1, which step 3 does not cite. Offered that, the step
    # elaborated and verified; it is not offered, so nothing says k ∈ ℂ.
    ('lean on a line the step does not name',
     'proof/sqrt2-irrational/odd-square',
     'proof/sqrt2-irrational.proof',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: from 1\n',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n',
     'proof/sqrt2-irrational.proof:13  nothing says m e. CC, which this '
     'step needs'),

    # A requires line rests only on its reason. Line 2 does not say k is an
    # integer, and `thm:stdlib/numbers/int-real` asks it; the scope has it from line 1,
    # which the line does not cite, so the item it names reaches nothing.
    ('give a requires line a reason that is not where its proof comes from',
     'proof/sqrt2-irrational/odd-square',
     'proof/sqrt2-irrational.proof',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: from 1\n',
     '3.  (2k + 1)² = 4k² + 4k + 1\n'
     '    algebra\n'
     '    requires k ∈ ℝ: thm:stdlib/numbers/int-real, from 2\n',
     'proof/sqrt2-irrational.proof:13  thm:stdlib/numbers/int-real targets '
     'zre, and none '
     'of them reaches m e. RR'),

    # Everything a step names does work. 2 is a numeral, not an atom, so
    # `algebra` asks nothing about its being real, and the kernel has it
    # from the library; the line is true, well formed, and does nothing.
    ('write a requires line nothing asks for',
     'proof/sum-formula/sum-formula',
     'proof/sum-formula.proof',
     '                  requires 2 ≠ 0: arithmetic\n',
     '                  requires 2 ≠ 0: arithmetic\n'
     '                  requires 2 ∈ ℝ: arithmetic\n',
     'says 2 ∈ ℝ, and the step neither uses nor asks for it'),

    # The certificate combines lines 3 and 4; line 1 says a + b ∈ ℝ, which
    # the step writes as its atoms instead, and is cited for nothing.
    ('cite a line a method step does not combine',
     'proof/triangle-inequality/triangle-inequality',
     'proof/triangle-inequality.proof',
     '    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 3, 4\n',
     '    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 1, 3, 4\n',
     'step 5.2 cites 1 and uses nothing it says'),

    # Each atom a method combines is real, and the step says so. The
    # kernel's `ltne` never needs d ∈ ℝ here, so nothing else would see the
    # line gone: only what the method asks for does.
    ('leave out the membership of an atom the method combines',
     'proof/sqrt2-irrational/lowest-terms',
     'proof/sqrt2-irrational.proof',
     '    3.7.  d ≠ 1\n          inequalities, from 3.1\n'
     '          requires d ∈ ℝ: from 3.1\n',
     '    3.7.  d ≠ 1\n          inequalities, from 3.1\n',
     'step 3.7 combines d, and nothing it writes or cites says it is a '
     'number'),

    # `decide_field` refuses a claim that is not an identity. It is raised
    # outside the handler that falls back to stating the step, and must
    # stay that way.
    ('claim an algebra step the cited lines do not give',
     'proof/geometric-series/geometric-sum',
     'proof/geometric-series.proof',
     '    2.10.6. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = '
     '(1 − a^(k + 1)·a)/(1 − a)',
     '    2.10.6. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = '
     '(1 − a^(k + 1)·a)/(1 − a) + 1',
     'is not an identity'),

    # A side condition is searched for among what the step names, not among
    # everything in scope. Without 1.2.1.5 the step still needs T finite,
    # and the scope holds |T| = 2^k: offered it, the search found the route
    # and R1 refused it afterwards, so which route the search took decided
    # whether a correct page was reported. It must not be offered at all.
    ('settle a side condition from a line the step does not cite',
     'proof/subsets/subsets-count',
     'proof/subsets.proof',
     'n := 2^k, from 1.2.1.3, 1.2.1.5, 1.2.1.6',
     'n := 2^k, from 1.2.1.3, 1.2.1.6',
     'no clause of thm:stdlib/counting/card-disjoint-union reaches what step 1.2.1.8 '
     'claims'),

    # An item taken as stated is stated as the item says it. Stating the
    # step's claim under the item's hypotheses instead assumed whatever the
    # step claimed, and the kernel accepts whatever is assumed. No step in
    # the corpus cites an item taken as stated for a claim it could get
    # wrong, so one is made: `card-remove` loses its target and says less
    # than step 1.2.1.2 claims of it.
    ('claim what an item taken as stated does not state',
     'proof/subsets/subsets-count',
     'stdlib/counting.records',
     '  then        |X ∖ {a}| = k\n'
     '  metamath    hashdifsnp1\n'
     '  target      hashdifsnp1 with V := X, N := a, Y := k\n',
     '  then        |X ∖ {a}| ≤ k\n'
     '  metamath    hashdifsnp1\n',
     'thm:stdlib/counting/card-remove is taken as stated and states'),

    # A definition with no target is stated as the definition says it and
    # the claim read off one side. Stating the claim under the cited lines
    # took whatever the step claimed, and only a later step using it could
    # notice.
    ('unfold a definition taken as stated into what it does not say',
     'proof/intermediate-value/intermediate-value',
     'proof/intermediate-value.proof',
     '10. For every s ∈ S, s ≤ c.',
     '10. For every s ∈ S, s < c.',
     'def:stdlib/calculus/upper-bound is taken as stated and states'),

    # `elcncf2` is read in the page's words, which is a reading and not a
    # licence: continuity with δ where ε belongs, or with δ ≥ 0 where the
    # definition says δ > 0, is not what it says.
    ('unfold continuity into what it does not say',
     'proof/intermediate-value/intermediate-value',
     'proof/intermediate-value.proof',
     'if |x − c′| < δ then |f(x) − f(c′)| < ε.',
     'if |x − c′| < δ then |f(x) − f(c′)| < δ.',
     'proof/intermediate-value.proof:73  no method owns this step: '
     'elcncf2 does not say'),

    ('unfold continuity with a weaker bound than it gives',
     'proof/intermediate-value/intermediate-value',
     'proof/intermediate-value.proof',
     'there is δ ∈ ℝ with δ > 0 and',
     'there is δ ∈ ℝ with δ ≥ 0 and',
     'elcncf2 does not say'),

    # The least upper bound is the supremum, which is a number only of a
    # set bounded above, and line 7 is what says S is. Without it cited
    # nothing names a bound, and the step says which.
    ('obtain the least upper bound without the line bounding the set',
     'proof/intermediate-value/intermediate-value',
     'proof/intermediate-value.proof',
     'obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7',
     'obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2',
     'proof/intermediate-value.proof:47  no cited line names a witness '
     'for E. x e. RR'),

    # Each part of what the claim asks of the witness is one of the
    # target's lemmas, and a part none of them reaches is the target
    # failing, not something to take as stated.
    ('leave out the lemma saying the supremum is least',
     'proof/intermediate-value/intermediate-value',
     'stdlib/calculus.records',
     '  target      suprcl, suprub, suprleub with c := sup S',
     '  target      suprcl, suprub with c := sup S',
     'thm:stdlib/calculus/completeness targets suprcl, suprub, and none of '
     'them reaches what step 8 obtains'),

    # `arithmetic` works a closed claim out before proving it, and takes
    # nothing as stated. A false one used to be stated as an axiom, and one
    # of digits alone crashed the normaliser on the way.
    ('claim a false numeral fact with a number past one digit',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     'requires 10^0 − 1 = 3·0: arithmetic',
     'requires 10^0 − 1 = 3·1: arithmetic',
     'claims 10^0 − 1 = 3·1, which is false'),

    ('claim a false numeral fact of digits',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     'requires 9 = 3·3: arithmetic', 'requires 9 = 3·4: arithmetic',
     'claims 9 = 3·4, which is false'),

    # True, and past what the method shows while it reads digits alone: a
    # theorem stating it is what the page cites, and saying so is the
    # report, where the fact used to be stated.
    ('ask arithmetic for a true fact it cannot show',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     '10 − 1 = 9\n                  thm:stdlib/numbers/ten-minus-one',
     '10 − 1 = 9\n                  arithmetic',
     'step 1.3.4 claims 10 − 1 = 9, which is true, and arithmetic cannot '
     'show it yet'),

    # What has no exact value is refused before anything is computed or
    # stated: a division by zero, a number too large to work out, which
    # would run for as long as memory lasts, and a power that is not a
    # rational, which a float would otherwise have decided.
    ('divide by zero in a numeral fact',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     '                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.',
     '                  requires 10 ∈ ℝ: arithmetic\n'
     '                  requires 3/0 ∈ ℝ: arithmetic\n\n          1.3.8.',
     'which divides by zero'),

    ('state a numeral too large to work out',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     '                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.',
     '                  requires 10 ∈ ℝ: arithmetic\n'
     '                  requires 9^(9^9) ∈ ℕ: arithmetic\n\n          1.3.8.',
     'which is too large to work out'),

    ('raise a numeral to a power that is not whole',
     'proof/divisibility-by-three/ten-power-congruent',
     'proof/divisibility-by-three.proof',
     '                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.',
     '                  requires 10 ∈ ℝ: arithmetic\n'
     '                  requires 4^(1/2) ∈ ℕ: arithmetic\n\n          1.3.8.',
     'which is not a rational number'),

    # Named where it is used, `arithmetic` works the fact out first, as it
    # does a step of its own: a false one is reported, never rewritten by.
    ('substitute by a false fact of numerals',
     'proof/geometric-series/geometric-sum',
     'proof/geometric-series.proof',
     'substitute 0 + 1 = 1 (arithmetic)',
     'substitute 0 + 1 = 2 (arithmetic)',
     'step 2.4 substitutes 0 + 1 = 2, which is false'),

    ('a chain link of numerals that is false',
     'proof/sum-formula/sum-formula',
     'proof/sum-formula.proof',
     '= 1(1 + 1)/2            arithmetic',
     '= 1(1 + 1)/3            arithmetic',
     'a link of step 1.2 claims 1 = 1(1 + 1)/3, which is false'),

    # `membership` builds from what the line cites: ε > 0 does not say ε is
    # a real number, and the scope's copy of the line that does is not
    # the requires line's to use unnamed.
    ('membership from a line that says nothing of the atom',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     'requires ε/2 ∈ ℝ: membership, from K3',
     'requires ε/2 ∈ ℝ: membership, from A1',
     'rests on K3, which it does not name'),

    # A sum's terms are built for each index in its range, and from 0 the
    # first of them divides by T(0), which nothing says is not zero.
    ('membership of a sum whose first term divides by zero',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     '                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: membership\n'
     '                  requires ε ∈ ℝ: from K3\n'
     '                  requires n ∈ ℝ: from K4\n'
     '                  requires n + 1 ≠ 0: inequalities, from K4\n'
     '                  requires N ∈ ℝ: from 3.2',
     '                  requires Σ(k = 0 to n) 1/T(k) ∈ ℝ: membership\n'
     '                  requires ε ∈ ℝ: from K3\n'
     '                  requires n ∈ ℝ: from K4\n'
     '                  requires n + 1 ≠ 0: inequalities, from K4\n'
     '                  requires N ∈ ℝ: from 3.2',
     'is not built from what the requires line cites'),

    # Said of every member, a term's divisor must not be zero for each: k ∈ ℤ
    # gives no k ≠ 0.
    ('membership said of every integer where a divisor may be zero',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     'requires for every k ∈ ℕ, 1/T(k) ∈ ℝ: membership',
     'requires for every k ∈ ℤ, 1/T(k) ∈ ℝ: membership',
     'is not built from what the requires line cites'),

    # A membership line says what the table in `rules.py` says it does and
    # nothing more: k ∈ ℤ gives no k ≠ 0, and n ∈ ℝ gives no n ∈ ℤ, since
    # the table goes one way.
    ('a membership read for a bound it does not give',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     '    let k ∈ ℕ                                                         (K1)',
     '    let k ∈ ℤ                                                         (K1)',
     'does not reach'),

    ('a membership read into a smaller number system',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     '    let n ∈ ℕ                                                         (K2)',
     '    let n ∈ ℝ                                                         (K2)',
     'does not reach'),

    # A link whose terms have a letter may name `arithmetic` where only a
    # piece of numerals alone changes, and that piece is worked out like
    # any closed fact: 2/1 is not 3.
    ('a chain link whose closed piece is false',
     'proof/triangular-reciprocals/triangular-reciprocals',
     'proof/triangular-reciprocals.proof',
     '= 2 − 2/(n + 1)                      arithmetic',
     '= 3 − 2/(n + 1)                      arithmetic',
     'which is false'),

    # `fsumdvds` asks that 3 divide each term, for k in the range, and line 1
    # says it for every k ∈ ℕ₀. Without line 1 cited nothing says it.
    ('sum what no cited line says each term of is divisible',
     'proof/divisibility-by-three/divisibility-by-three',
     'proof/divisibility-by-three.proof',
     'thm:stdlib/sums/sum-divisible m := 3, from H1, 1',
     'thm:stdlib/sums/sum-divisible m := 3, from H1',
     'no clause of thm:stdlib/sums/sum-divisible reaches what step 2 claims'),

    # A link of a calculation is what the line it cites says, and a line
    # saying something else is not taken for it: its proof would be of the
    # wrong statement, and only the verifier would notice.
    ('cite a line for a link it does not say',
     'proof/sum-formula/sum-formula',
     'proof/sum-formula.proof',
     '= k(k + 1)/2 + (k + 1)         1.3.3',
     '= k(k + 1)/2 + (k + 1)         1.3.2',
     '1.3.2 does not say'),

    # What says f is continuous is H5, and so is what says its domain and
    # codomain lie in ℂ, which `elcncf2` asks. Without it cited the step
    # has neither.
    ('unfold continuity without the line saying f is continuous',
     'proof/intermediate-value/intermediate-value',
     'proof/intermediate-value.proof',
     '    def:stdlib/calculus/continuous-on, from H5',
     '    def:stdlib/calculus/continuous-on',
     'proof/intermediate-value.proof:73  no method owns this step: no '
     'cited line is what elcncf2 unfolds'),

    # An item's target asks a side condition the page never writes, and
    # `rewritten` answers it through the equation the step cites: `0 < |X|`
    # is `0 < k + 1` by C2. Without C2 cited, the equation is in scope and
    # not in hand, and the side condition must go unanswered.
    ('answer a side condition by an equation the step does not cite',
     'proof/subsets/subsets-count',
     'proof/subsets.proof',
     'obtain a: thm:stdlib/counting/card-nonempty, from K2, C2',
     'obtain a: thm:stdlib/counting/card-nonempty, from K2',
     'thm:stdlib/counting/card-nonempty targets hashgt0elex, and none of them reaches'),

    # `elrnmpt1s` reads its map at a term only a cited line supplies. With
    # the line gone nothing says where the map is read, and the body must
    # not be read at the lemma's own variable instead.
    ('put something in an image without the line saying where it comes from',
     'proof/subsets/powerset-split',
     'proof/subsets.proof',
     's := V ∖ {a},\n                    from 1.3.2',
     's := V ∖ {a}',
     'no clause of thm:stdlib/functions/added-element-in-image reaches what step 1.3.3 '
     'claims'),

    # A target is where the claim lands, and a variable bound to the wrong
    # name makes it land somewhere else. That is reported, not assumed.
    ('bind a target variable to the wrong name',
     'proof/subsets/subsets-count',
     'stdlib/counting.records',
     '  target      hashdifsnp1 with V := X, N := a, Y := k',
     '  target      hashdifsnp1 with V := X, N := a, Y := X',
     'no clause of thm:stdlib/counting/card-remove reaches what step 1.2.1.2 '
     'claims'),

    # `sumeq2dv` forbids the sum's index in the scope, and the induction
    # hypothesis names it, so the lemma is proved one frame out. The line it
    # reads term by term is proved in the inner frame, and handed across it
    # was a proof of another statement: the step elaborated, the file said
    # nothing was assumed, and only the verifier refused it. An outer frame
    # is now offered only the lines it holds, and the step is reported.
    ('rewrite a sum term by term under a hypothesis naming its index',
     'proof/binomial/binomial',
     'proof/binomial.proof',
     '          1.8.4.  (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y) = '
     'Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n'
     '                  thm:binomial-step m := m, from H1, H2, K\n'
     '\n'
     '          1.8.5.  (x + y)^(m + 1) = Σ(k = 0 to m + 1) C(m + 1, k)·'
     'x^((m + 1) − k)·y^k\n'
     '                  calculation\n'
     '                    (x + y)^(m + 1) = (x + y)^m·(x + y)'
     '                                          1.8.2\n'
     '                                    = (Σ(k = 0 to m) C(m, k)·x^(m − k)·'
     'y^k)·(x + y)              1.8.3\n'
     '                                    = Σ(k = 0 to m + 1) C(m + 1, k)·'
     'x^((m + 1) − k)·y^k          1.8.4\n',
     '          1.8.4.  m ∈ ℤ\n'
     '                  thm:stdlib/numbers/nat0-int, from K\n'
     '\n'
     '          1.8.5.  For every k ∈ {0, …, m}, k + 0 = k.\n'
     '                  fix\n'
     '                  let k ∈ {0, …, m}'
     '                                   (J)\n'
     '\n'
     '                  1.8.5.1.  k ∈ ℤ\n'
     '                            thm:stdlib/sums/range-integer a := 0, b := m, '
     'from J\n'
     '                            requires 0 ∈ ℤ: arithmetic\n'
     '                            requires m ∈ ℤ: from 1.8.4\n'
     '\n'
     '                  1.8.5.2.  k ∈ ℝ\n'
     '                            thm:stdlib/numbers/int-real, from 1.8.5.1\n'
     '\n'
     '                  1.8.5.3.  k + 0 = k\n'
     '                            algebra\n'
     '                            requires k ∈ ℝ: from 1.8.5.2\n'
     '\n'
     '          1.8.6.  Σ(k = 0 to m) (k + 0) = Σ(k = 0 to m) k\n'
     '                  thm:stdlib/sums/sum-termwise a := 0, b := m, from 1.8.5\n'
     '                  requires 0 ∈ ℤ: arithmetic\n'
     '                  requires m ∈ ℤ: from 1.8.4\n'
     '\n'
     '          1.8.7.  (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y) = '
     'Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n'
     '                  thm:binomial-step m := m, from H1, H2, K\n'
     '\n'
     '          1.8.8.  (x + y)^(m + 1) = Σ(k = 0 to m + 1) C(m + 1, k)·'
     'x^((m + 1) − k)·y^k\n'
     '                  calculation\n'
     '                    (x + y)^(m + 1) = (x + y)^m·(x + y)'
     '                                          1.8.2\n'
     '                                    = (Σ(k = 0 to m) C(m, k)·x^(m − k)·'
     'y^k)·(x + y)              1.8.3\n'
     '                                    = Σ(k = 0 to m + 1) C(m + 1, k)·'
     'x^((m + 1) − k)·y^k          1.8.7\n',
     'no clause of thm:stdlib/sums/sum-termwise reaches what step 1.8.6 claims'),

    # A closed exponent's membership of ℕ₀ is placed through the digit it
    # comes to (`by_value`), and (0 − 1) − 0 comes to −1, which is no
    # digit and not in ℕ₀. The term's membership is refused, so the lemma
    # is, and the step is reported rather than the value looked up.
    ('a closed exponent that is not a whole number',
     'proof/binomial/binomial',
     'proof/binomial.proof',
     '    1.1.  Σ(k = 0 to 0) C(0, k)·x^(0 − k)·y^k = '
     'C(0, 0)·x^(0 − 0)·y^0\n',
     '    1.1.  Σ(k = 0 to 0) C(0, k)·x^((0 − 1) − k)·y^k = '
     'C(0, 0)·x^((0 − 1) − 0)·y^0\n',
     'no clause of thm:stdlib/sums/sum-single reaches what step 1.1 claims'),

    # A link reads its cited equation from either side, and nothing on the
    # page says which: line 2 says |CB| = |BC|, which is neither way round
    # the link's |CA| = |CB|.
    # A definition concluded of a value names that value: line 5 says what
    # n² is, and the step says n² is odd only by writing n := n². The pair
    # is found by its name, and it is not optional (`SYNTAX.md`).
    ('leave out the value a definition is concluded of',
     'proof/sqrt2-irrational/odd-square',
     'proof/sqrt2-irrational.proof',
     '    def:stdlib/divisibility/odd n := n², from 5',
     '    def:stdlib/divisibility/odd, from 5',
     'is about n, and the step gives n no value'),

    ('cite an equation that says the link neither way round',
     'proof/isosceles/isosceles',
     'proof/isosceles.proof',
     '           = |CB|       H5\n',
     '           = |CB|       2\n',
     '2 does not say |CA| = |CB|'),

    # A lemma's conclusion is carried to the claim through the standard
    # form, which reads eldifsn's u =/= a as the page's u ≠ a, down through
    # the ↔ and the "and" it sits in. It reads nothing else: a claim of
    # u = a in its place is still not what eldifsn says.
    ('claim what a lemma says with one relation changed',
     'tests/stdlib/sets/remove-member',
     'tests/stdlib/sets.proof',
     'then u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n\n'
     '1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n',
     'then u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n\n'
     '1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n',
     'no clause of thm:stdlib/sets/remove-member reaches what step 1 '
     'claims'),
]


# R1 and R2 are checked twice. `settle` is offered only what the step or
# the requires line names (`resting_on`), so the cases above that break a
# rule are caught by the search finding nothing; and once a proof is built,
# `rests_on_named` refuses one resting on anything else. The second is what
# catches a route that reads the scope without asking `settle` —
# `introduced` does, and so does `apply_lemma` matching an antecedent — and
# no case above reaches it, because the first always catches them sooner.
# So these run with the search offered everything in scope, and the rule
# afterwards is all that stands between the uncited line and the proof.
NETS = [
    # Step 1.2.1.8 needs T finite and no longer cites 1.2.1.5, which says
    # |T| = 2^k. Offered the whole scope, the search finds T finite through
    # that line, and with R1 taken away the step elaborates and verifies:
    # nothing else here objects, since the step cites an item and the
    # method checks do not apply.
    ('settle a side condition from a line the step does not cite, with '
     'nothing to stop the search',
     'proof/subsets/subsets-count',
     'proof/subsets.proof',
     'n := 2^k, from 1.2.1.3, 1.2.1.5, 1.2.1.6',
     'n := 2^k, from 1.2.1.3, 1.2.1.6',
     'step 1.2.1.8 rests on 1.2.1.5, which it does not name'),

    # The requires line's reason cites line 2, and `thm:stdlib/numbers/int-real` asks k
    # an integer, which line 1 says. With R2 taken away the step
    # elaborates.
    ('give a requires line a reason that is not where its proof comes '
     'from, with nothing to stop the search',
     'proof/sqrt2-irrational/odd-square',
     'proof/sqrt2-irrational.proof',
     '    requires k ∈ ℝ: from 1\n\n4.',
     '    requires k ∈ ℝ: thm:stdlib/numbers/int-real, from 2\n\n4.',
     'proof/sqrt2-irrational.proof:15  the requires line rests on 1, which '
     'it does not name'),
]


@contextlib.contextmanager
def whole_scope_offered():
    """`settle` offered every fact in scope, as it was before R1 existed."""
    @contextlib.contextmanager
    def unfiltered(_self, _allowed):
        yield

    kept = elaborate.Elaborator.resting_on
    elaborate.Elaborator.resting_on = unfiltered
    try:
        yield
    finally:
        elaborate.Elaborator.resting_on = kept


def run(root, wanted, setmm, net=False):
    """What elaborating says, or None where it says nothing and builds."""
    buf = io.StringIO()
    offered = whole_scope_offered() if net else contextlib.nullcontext()
    try:
        with redirect_stdout(buf), offered:
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
        for part in ('db', 'stdlib', 'proof', 'tests', 'parley',
                     'elaboration'):
            shutil.copytree(ROOT / part, clean / part,
                            ignore=shutil.ignore_patterns('__pycache__'))

        # The corpus is clean, so the theorem must elaborate before the
        # edit. A case that fails here is testing nothing. Asked once per
        # theorem rather than once per case: the corpus is the same corpus
        # each time, and five of these cases are about one theorem that
        # takes ten seconds to elaborate.
        healthy = {}
        planted = [(case, False) for case in CASES] + \
                  [(case, True) for case in NETS]
        for (name, wanted, rel, old, new, expect), net in planted:
            if (wanted, net) not in healthy:
                healthy[wanted, net] = run(clean, wanted, setmm, net)
            if healthy[wanted, net] is not None:
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
            said = run(work, wanted, setmm, net)
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

    print(f'\n{passed} caught, {failed} missed, of {len(planted)} planted '
          f'defects')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
