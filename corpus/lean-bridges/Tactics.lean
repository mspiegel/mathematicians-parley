module

public import Mathlib
public import Factorials

/-!
# Tactics the generated proofs use

Each closes a goal of one kind the page leaves to its reader, and is named
for that kind, so a generated proof says what it asks and the search for
how is written once, here. Every alternative closes the goal or fails:
`ring`, `norm_num` and `apply` can succeed while leaving a goal open, so
each alternative ends in `done`, and `ring1` is used for `ring`.
-/

public section

/-- An integer not negative, cast to any ring from the natural number its
`toNat` is, is itself: the build gives a natural letter an integer the page
shows is not negative as its `toNat` (`theorem::witness`). -/
theorem parley_cast_toNat {R : Type*} [Ring R] {n : ℤ} (h : 0 ≤ n) :
    ((n.toNat : ℕ) : R) = (n : R) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-- An order between numbers that follows from the lines above by linear
arithmetic, as an `inequalities`, `transitivity` or `antisymmetry` step's
does: the ways of `parley_side` that close such a goal, the cheapest first,
and none that do not. -/
macro "parley_order" : tactic =>
  `(tactic| ((try cases_type* And) <;> (try casesm* _ ∧ _) <;> first
    | (assumption; done)
    | (constructor <;> assumption; done)
    | (positivity; done)
    | (omega; done)
    | (linarith; done)
    -- Natural numbers in ℝ, 2 ≤ N + 1 from 0 < N: the casts moved out.
    | (norm_cast at *; omega; done)
    | (push_cast at *; assumption; done)
    | (assumption_mod_cast; done)
    | (push_cast at *; linarith; done)
    | (qify at *; linarith; done)
    | (rify at *; linarith; done)
    | (norm_num at *; omega; done)
    | (apply lt_of_le_of_ne <;> (first | linarith | assumption | (apply Ne.symm; assumption)); done)
    -- Quotients as products with an inverse, so that 4/n and 1/2^n meet
    -- 1/n and (2^n)⁻¹ as the same terms.
    | (simp only [div_eq_mul_inv, one_mul] at *; linarith; done)))

/-- What a page leaves to its reader: a side condition of a cited item, a
membership said once, a line restated or joined from lines above, or a
block's last line taken as what the block owes. The lines above are taken
apart at each "and" first: `cases_type* And` leaves whole an "and" beside a
`Set.InjOn` (it reports no match), which `casesm* _ ∧ _` takes apart. -/
macro "parley_side" : tactic =>
  `(tactic| ((try cases_type* And) <;> (try casesm* _ ∧ _) <;> first
    | (assumption; done)
    -- An integer in ℕ₀, said `0 ≤ x` of an integer and `∃ m : ℕ, ↑m = x`
    -- where an item over any ring says it. Tried only on such a goal: on
    -- another, d ∣ 1 among them, the unifying recurses past Lean's limit,
    -- which ends `first`.
    | (show ∃ _ : ℕ, _; exact ⟨_, Int.toNat_of_nonneg (by omega)⟩; done)
    | ((cases_type* Exists); omega; done)
    -- A line that says the goal with its casts set otherwise, ((n : ℤ) : ℝ)
    -- for (n : ℝ), as an item on a range of integers gives a sequence's term.
    | (push_cast at *; assumption; done)
    | (apply Eq.symm; assumption; done)
    | (apply Ne.symm; assumption; done)
    | (constructor <;> assumption; done)
    | (constructor <;> assumption_mod_cast; done)
    -- Two sides that differ only in where a cast stands, x ↑(n + 1) and
    -- x (↑n + 1).
    | (push_cast; done)
    -- Something said of every integer of a range from 1, given of every
    -- natural number: each such integer is a natural above 0.
    | (intro k; intros; (try simp only [Finset.mem_Icc] at *); lift k to ℕ using (by omega);
        push_cast; apply_assumption; omega; done)
    | (positivity; done)
    | (omega; done)
    | (linarith; done)
    | (assumption_mod_cast; done)
    | (push_cast at *; linarith; done)
    | (qify at *; linarith; done)
    | (rify at *; linarith; done)
    | (apply lt_of_le_of_ne <;> (first | linarith | assumption | (apply Ne.symm; assumption)); done)
    | (norm_num at *; done)
    | (norm_num at *; subst_vars; norm_num; done)
    | (norm_cast at *; subst_vars; norm_num; done)
    | (norm_num at *; omega; done)
    | (norm_num at *; norm_cast at *; omega; done)
    | (contradiction; done)
    | (exfalso; apply ‹¬ _›; exact Int.ModEq.symm ‹_›; done)
    -- An integer a line gives as a quotient, (M! + 1)/N, in an equation of
    -- integers: in ℚ, with the division cleared, it is linear.
    | (qify at *; field_simp at *; linarith; done)
    -- A line about every natural number, in another type than the goal's:
    -- (n : ℚ) ≤ 2^n from "for all k ∈ ℕ, k ≤ 2^k" in ℤ, each cast moved
    -- out and the line applied.
    | (norm_cast at *; solve_by_elim; done)
    | (simp_all; done)))

/-- `parley_suppose h`, where `h` denies what a contradiction block claims:
proves the block's `suppose` line, which says the same as `h` in the words
the page chose. -/
macro "parley_suppose " h:ident : tactic =>
  `(tactic| first
    | (exact $h; done)
    | (exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact $h; done)
    | (push_neg at $h:ident; linarith; done)
    | (simpa using $h; done)
    | (simp only [not_not] at $h:ident; exact $h; done)
    | (simp only [not_not, ne_eq] at $h:ident; exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact Eq.symm $h; done)
    | (intro _; apply $h; simp_all; done))

/-- `arithmetic`: a closed fact of numbers, worked out, and that a fraction
which is no whole number is no member of ℕ or ℤ. -/
macro "parley_arith" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | (norm_num [LeanBridges.Counting.factorial, LeanBridges.Counting.choose, Nat.factorial]; done)
    -- A sum or a product of integers over a range of numerals, which Lean
    -- works out term by term.
    | (decide; done)
    | (rintro ⟨m, _, h⟩; field_simp at h; norm_cast at h; omega)
    | (rintro ⟨m, h⟩; field_simp at h; norm_cast at h; omega))

/-- Clears what an `algebra` step divides by, from the lines saying each
divisor is not 0, a product, a quotient or a negation not 0 taken as each
of its parts not 0. A natural number above 0, the q of p/q, is not 0. -/
macro "parley_clear" : tactic =>
  `(tactic| ((try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or,
      pow_eq_zero_iff, Nat.pos_iff_ne_zero] at *) <;> (try cases_type* And) <;> field_simp))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
-- The check `linear_combination` ends with: `ring1`, or `ring1` after the
-- casts are pushed in, where a function's argument is cast two ways,
-- C(↑m + 1, 1) beside C(↑(m + 1), 1), which ring1 takes as two atoms.
macro "parley_norm" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A function of numerals written two ways, (1 + 1)! beside 2!.
    | (norm_num [LeanBridges.Counting.factorial, Nat.factorial]; done))

macro "parley_ring" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A factorial divided by itself, which is not 0.
    | (field_simp [LeanBridges.Counting.factorial, Nat.factorial_ne_zero]; done)
    | (simp only [inv_inv, one_div, div_div, div_pow] <;> ring1; done)
    | (parley_clear <;> ring1; done)
    | (parley_clear; done))

/-- `substitute`, into the goal: the goal is what the equation `e` makes of
a term in it, either way round. -/
macro "parley_subst " e:term:max : tactic =>
  `(tactic| first
    | (rw [$e:term]; done)
    | (rw [← $e:term]; done)
    | (rw [$e:term]; ring1; done)
    | (rw [← $e:term]; ring1; done)
    | (simp only [$e:term]; done)
    | (simp only [← $e:term]; done)
    | (simp only [$e:term]; ring1; done)
    | (simp only [← $e:term]; ring1; done)
    | (linear_combination $e:term; done)
    | (linear_combination (-1 : _) * $e:term; done)
    | (have h := $e:term; norm_cast at h; rw [h]; done)
    | (have h := $e:term; norm_cast at h; rw [← h]; done)
    | (have h := $e:term; norm_cast at h; simp only [h]; done))

/-- `parley_subst_at e h` by rewriting, with no `simp` by `e`. That loops where one side of
`e` stands inside the other, b in gcd(a, b), and `first` does not go on past
a loop, so a step offering several lines tries this on each before
`parley_subst_at` on any. -/
macro "parley_put_at " e:term:max h:ident : tactic =>
  `(tactic| first
    | (rw [$e:term] at $h:ident; exact $h; done)
    | (rw [← $e:term] at $h:ident; exact $h; done)
    -- `rw` closes a goal its rewriting leaves reflexive, b ∣ b, itself.
    | (rw [$e:term]; (try exact $h); done)
    | (rw [← $e:term]; (try exact $h); done)
    -- A fact of naturals, b > 0 as `0 < b`, put into by an equation of
    -- integers: the fact is taken up to ℤ first.
    | (have h' := $h; zify at h'; rw [← $e:term] at h'; exact h'; done)
    | (have h' := $h; zify at h'; rw [$e:term] at h'; exact h'; done)
    -- A fact or an equation of numerals alone, written in ℚ, put where
    -- the other is in ℝ, (√(1/4))² for 1/4: taken up to ℝ first.
    | (have h' := $h; rify at h'; first | (rw [← $e:term] at h'; exact h') | (rw [$e:term] at h'; exact h'); done)
    | (have e' := $e; rify at e'; first | (rw [← e'] at $h:ident; exact $h) | (rw [e'] at $h:ident; exact $h); done)
    -- An equation of naturals cast up to ℤ, put where ℕ is wanted, an
    -- exponent, is taken back down first.
    | (have e := $e; norm_cast at e; rw [← e] at $h:ident; exact $h; done)
    | (have e := $e; norm_cast at e; rw [e] at $h:ident; exact $h; done)
    | (rw [$e:term] at $h:ident; linarith; done)
    | (rw [← $e:term] at $h:ident; linarith; done)
    -- What the putting leaves to tidy, a 0 + x of a term put to 0.
    | (rw [$e:term] at $h:ident; simpa using $h; done)
    | (rw [$e:term] at $h:ident; parley_side; done)
    | (rw [← $e:term] at $h:ident; parley_side; done)
    | (rw [$e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term]; exact $h _; done)
    | (rw [$e:term]; exact $h _; done)
    | (exact $h _; done))

/-- `substitute` into the line `h`: the goal is `h` with a term put for
another by the equation `e`, either way round. -/
macro "parley_subst_at " e:term:max h:ident : tactic =>
  `(tactic| first
    | (parley_put_at $e $h; done)
    | (simp only [$e:term] at $h:ident ⊢; exact $h; done)
    | (simp only [← $e:term] at $h:ident ⊢; exact $h; done)
    | (simp only [$e:term] at $h:ident ⊢; linarith; done)
    | (simp only [← $e:term] at $h:ident ⊢; linarith; done))

/-- An equation `h` an item gives of natural exponents, given an integer's
`toNat` for one, read at the claim's integer exponents: 2^(n − 1 + 1) with
n − 1 an integer that a line shows not negative, which `omega` proves. An
equation of integers is taken to ℚ first, where integer powers are. -/
macro "parley_int_power " h:ident : tactic =>
  `(tactic| first
    | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg] at $h:ident; linear_combination (norm := parley_norm) ($h:ident); done)
    | (have q := congrArg (fun x : ℤ => (x : ℚ)) $h:ident; push_cast at q;
        simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg] at q; linear_combination (norm := parley_norm) q; done))

/-- What `linear_combination` asks once the cited equations are subtracted,
where the step divides: zero, once the divisions are cleared. -/
macro "parley_field" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A divisor said not 0 in its own least type, 3 * (n : ℤ) - 1 ≠ 0, and
    -- divided by in ℝ, written the other way round, ↑n * 3 - 1: the facts
    -- cast up and both normalised, field_simp sees they are one.
    | ((try rify at *); ring_nf at *; field_simp; ring1; done)
    -- Divisors field_simp does not clear, 3n − 1 beside a fact that says it
    -- is not 0: the fractions are joined and multiplied out one at a time,
    -- each divisor shown not 0 from the facts.
    | ((try push_cast at *); (try rify at *);
        simp (disch := simp_all) only [div_add_div, div_sub_div, div_eq_div_iff, eq_div_iff,
          div_eq_iff, mul_one_div, mul_div_assoc', div_mul_eq_mul_div, div_add', add_div',
          div_sub', sub_div']; ring1; done)
    | (parley_clear <;> ring1; done))

end
