# Pilot: the ballot problem

Theorem 40 of `SELECTION.md`, Wiedijk #30, set.mm's `ballotth` (a mathbox
theorem whose definitions are hypotheses, so it is not cited):

  if A gets m votes and B gets n < m, and the votes are counted in an order
  chosen at random, all orders alike, the chance that A is ahead after
  every vote is (m − n)/(m + n).

A counting is given by the places among the first m + n at which A's votes
come: O is the parts of {1, …, m + n} with m elements, and E those c in
which, after every i votes, B's count |{1, …, i} ∖ c| is less than A's,
|{1, …, i} ∩ c|. The theorem is |E|/|O| = (m − n)/(m + n).

The proof is Bertrand's of 1887, by induction on the number of votes,
rather than André's reflection: a counting ends with a vote for A or for
B, and taking it away leaves a good counting with one vote fewer.
Reflection needs the first tie of each counting as a function of the
counting, which the language has no way to write: there is no "the least"
term, and a bijection is only ever stated, by `image-of-injection`, for the
one map S ↦ S ∪ {a}. The induction needs only that map.

---

## Theorems

The proof is `proofs/wiedijk/ballot.proof`. A define above the theorems
names the good countings with m votes for A and n for B:

    define G(m, n) := {c ∈ {d ⊆ {1, …, m + n} : |d| = m} : for all i ∈ {1, …, m + n},
        |{1, …, i} ∖ c| < |{1, …, i} ∩ c|}, for m ∈ ℕ₀, n ∈ ℕ₀

(one line in the file). Thirteen theorems, each built to
`corpus/elaboration/proofs/wiedijk/ballot/`, assuming nothing:

- `good-finite`: G(m, n) is finite.
- `last-place`: at the last place B has n votes and A m.
- `lead-to-the-end`: ahead before the last place and n < m, ahead at it.
- `prefix-unchanged`: a vote after place i changes nothing up to i.
- `places-before-last`: {1, …, p} = {1, …, N} ∖ {N} where p + 1 = N.
- `tie-at-the-end`: G(m, m) = ∅.
- `no-votes-for-b`: |G(m, 0)| = 1, by #58: the one counting is all A.
- `add-last-place`: T ↦ T ∪ {m + n} is one-to-one on G(m − 1, n).
- `last-vote-for-a`: the good countings ending with A are those of
  G(m − 1, n) with m + n put back.
- `last-vote-for-b`: those ending with B are G(m, n − 1).
- `ballot-recurrence`: the formula at m − 1, n and at m, n − 1 gives it at
  m, n, for 1 ≤ n < m, by the split by the last vote, Pascal's rule and the
  absorption identity.
- `ballot-count`: |G(a, b)|·(a + b) = (a − b)·C(a + b, a) for b ≤ a, by
  induction on the number of votes.
- `ballot`: the theorem, with |O| = C(m + n, m) by #58.

---

## Rendered view

**Theorem.** Let m, n ∈ ℕ with n < m, O = {c ⊆ {1, …, m + n} : |c| = m}
and E = {c ∈ O : for all i ∈ {1, …, m + n}, |{1, …, i} ∖ c| <
|{1, …, i} ∩ c|}. Then |E|/|O| = (m − n)/(m + n).

*Proof.* Write G(a, b) for E with a votes for A and b for B. We show
|G(a, b)|·(a + b) = (a − b)·C(a + b, a) for b ≤ a, by induction on a + b.

1. a + b = 0: both sides are 0.
2. b = a ≥ 1: at the last place the two are level, so G(a, a) = ∅, and
   both sides are 0.
3. b = 0 < a: the one counting puts every vote for A, and it is good, so
   |G(a, 0)| = C(a, a) = 1 and both sides are a.
4. 1 ≤ b < a, with N = a + b: a good counting's last vote is for A or for B.
   - Ending with A, it is a good counting of a − 1 and b with N put last:
     the last vote changes no count before the last place, and at the last
     place A has a > b. So these number |G(a − 1, b)|.
   - Ending with B, it is a good counting of a and b − 1, and at the last
     place A again has a > b. So these number |G(a, b − 1)|.
   - By the hypothesis, |G(a − 1, b)|·(N − 1) = (a − 1 − b)·C(N − 1, a − 1)
     and |G(a, b − 1)|·(N − 1) = (a − b + 1)·C(N − 1, a).
   - N·C(N − 1, a − 1) = a·C(N, a) by absorption, and N·C(N − 1, a) =
     b·C(N, a) by Pascal's rule. So |G(a, b)|·(N − 1)·N =
     ((a − 1 − b)·a + (a − b + 1)·b)·C(N, a) = (a − b)·(N − 1)·C(N, a),
     and N − 1 ≠ 0 cancels.

Then |E|·(m + n) = (m − n)·C(m + n, m), and |O| = C(m + n, m) ≠ 0 by
#58. ∎

---

## Database items

In `corpus/stdlib/counting.records`, mundane: `card-difference`
(`hashssdif`), |X ∖ Y| = |X| − |Y| for Y ⊆ X finite. The proof also cites
`binomial-nat` (`bccl2`), which the Ramsey pilot added.

In `corpus/stdlib/sets.records`, each mundane: `set-builder-empty`
(`rabeq0`), `singleton-outside` (`disjsn`), `difference-by-union`
(`difun1`), `nothing-left-outside` (`ssdif0`), `intersection-of-part`
(`sseqin2`); and `set-builder-split` and `set-builder-split-disjoint`,
which the Ramsey pilot added.

In `corpus/stdlib/sums.records`, each mundane: `range-without-last`
(`fzdifsuc`), `range-end` (`elfz1end`), `range-within` (`fzss2`).

---

## What the pilot reveals

1. **A part of a range has its sort.** {d ⊆ {1, …, m + n} : |d| = m}
   left d of no sort, and |d| did not read; a set written as a term is now
   read as the parser reads it (`tests/front_end.rs`,
   `a_part_of_a_range_is_a_set`).
2. **A set-valued define is a set where its statement is cited.** A
   theorem stated with |G(m, n)| was read, where another step cited it,
   with G's value of no sort, so every citation "did not conclude" the
   claim. A define's value now has the sort its rule was read with
   (`a-set-valued-define-sized.proof`).
3. **A define applied in a cited line asks its domain.** `T ∈ G(m − 1, n)`
   unfolded by citing G's define is G's rule only where m − 1 ∈ ℕ₀. The
   checker now asks it of the lines the step cites, as of the claim, where
   the argument is not a letter the line binds.
4. **The build reads a define of two arguments inside a cited line.** It
   unfolds `c ∈ G(m, n)` by G's rule, carries a change in a set-builder's
   condition and domain at once (`rabeqbidv`), renames a set-builder whose
   domain binds letters too, and closes x + 0 against x where x is a
   number (`a-family-of-parts-by-a-define.proof`).
5. **An instance whose condition is an identity needs no line.**
   Instantiating k := a + b in "if k = a + b and …" asks a + b = a + b,
   which `SYNTAX.md` says needs no line; the checker asked a line for it
   (`an-instance-whose-condition-is-itself`).
6. **A hypothesis that applies a define is read by its names.**
   `ballot-recurrence` assumes |G(m − 1, n)|·… = …, which the kernel holds
   written out by G's rule. A step putting an equation into it, or citing
   it, reads it with the name, where the step's `requires m − 1 ∈ ℕ₀` says
   the argument is in G's domain
   (`tests/elaborator/a-define-applied-in-a-hypothesis.proof`). Before
   this, the recurrence had to be two theorems, the set fact and the
   arithmetic over plain numbers.
7. **A conclusion that applies a define has its domains said.**
   `add-last-place` concludes of G(m − 1, n); a hypothesis or a line of the
   proof outside any block says m − 1 ∈ ℕ₀, since the build reaches the
   statement with what the proof holds at its outermost level. The checker
   asks for it (`check_conclusion_domains`). It does not yet ask, where a
   step cites a theorem of the same file stated over a define, for the
   domain of the define's argument there: the build asks it, and the
   checker cannot yet tell it from a domain the build reaches through the
   define's rule, as `reals-uncountable` does.
8. **No reflection.** The language has no "least element" term and no
   general bijection, so André's argument cannot be written.

Numbers, for the record: 303 numbered steps over thirteen theorems, 15
requires lines.
