module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Rify
public import ParleySimp
public import PowerTactics
public import Divisibility

/-!
# A cited item read as the step writes its lines

An item's Lean statement is written once, over any ring `K` or any set `X`;
the step's lines are written by the theorem's writer from the page. At a
citation the two can spell one fact differently: `x ^ e.toNat` beside
`x ^ e`, `m ∈ {n : ℤ | 0 < n}` beside `0 < m`, `∀ x ∈ Set.univ` beside
`∀ x`, an item in ℂ or ℝ beside a line in ℝ or ℚ. `parley_instance` reads
the item's statement in the step's spelling by the facts that join them, the
simp set `parley_spelling`, and closes the step's statement of it. A fact
found missing is tagged into the set here, never added at a step.
-/

public section

/-- A product over a range written as a set, as an item over any set writes
it, is the product over the range as a finite set, as the step writes it. -/
theorem parley_finprod_Icc {M : Type*} [CommMonoid M] (a b : ℤ) (f : ℤ → M) :
    (∏ᶠ x ∈ (Set.Icc a b : Set ℤ), f x) = ∏ x ∈ Finset.Icc a b, f x := by
  rw [← Finset.coe_Icc, finprod_mem_coe_finset]

/-- The same of a sum. -/
theorem parley_finsum_Icc {M : Type*} [AddCommMonoid M] (a b : ℤ) (f : ℤ → M) :
    (∑ᶠ x ∈ (Set.Icc a b : Set ℤ), f x) = ∑ x ∈ Finset.Icc a b, f x := by
  rw [← Finset.coe_Icc, finsum_mem_coe_finset]

/- Each a representation fact: a cast of a term to its own type; ℕ or ℕ₀
said as some integer; membership of a set built by a condition; a whole type
as a set; a range as a set and as a finite set, a product or sum over it
included; an order either way round; the norm of a real; an integer power to
an exponent the lines in scope show not negative; the reals' `mod` of
integers as their `%`; 1 + 1 of a field as 2, which no procedure works out
there. -/
attribute [parley_spelling] Int.cast_id exists_eq_right Set.mem_ofPred_eq
  Set.mem_sep_iff Set.sep_ofPred Set.mem_univ Set.univ_inter Set.inter_self
  true_and and_true true_implies Filter.univ_mem Set.mem_Icc Finset.mem_Icc ge_iff_le
  gt_iff_lt Complex.norm_real Real.norm_eq_abs parley_zpow_toNat
  LeanBridges.Divisibility.mod_intCast parley_finprod_Icc parley_finsum_Icc
  one_add_one_eq_two

/-- `parley_instance e`: the cited item `e`, at the citation's values, as
the step's own statement of it, the two in one number type. A product or sum
over a range written as a set is read as one over the finite set first, before
`Set.mem_Icc` takes the range apart; the casts of both are pushed down to the
letters, `↑(1 + 1)` as `1 + 1`, so the set's arithmetic facts meet them; then
both are read by `parley_spelling` and a numeral's `toNat` worked out
(`Int.reduceToNat`, a procedure no set can hold), the facts an integer power
asks by `omega` from the lines in scope, and where that leaves the step open
the casts are pushed down again and the two meet as written. Each step after
the first acts on the step only while it is open: one that says `x = x` is
closed on the way. Lifting the casts instead would read a division of casts
one way on one side and another on the other. -/
macro "parley_instance " e:term:max : tactic =>
  `(tactic| (
    have h := $e:term
    simp -failIfUnchanged only [parley_finprod_Icc, parley_finsum_Icc] at h ⊢
    all_goals push_cast at h ⊢
    all_goals simp -failIfUnchanged (disch := omega) only
      [parley_spelling, Int.reduceToNat] at h ⊢
    all_goals (push_cast at h ⊢; exact h)))

/-- `parley_instance_cast e`: as `parley_instance`, the item stated in a
wider type than the step, ℂ at reals, ℝ at rationals or integers: the item's
casts lifted out first, `↑A + ↑M * 1` as `↑(A + M * 1)` (`norm_cast`), then
read by `parley_spelling` (the reals' `mod` of integers their `%` among it),
and the two met by moving their casts alike (`exact_mod_cast`). -/
macro "parley_instance_cast " e:term:max : tactic =>
  `(tactic| (
    have h := $e:term
    norm_cast at h
    all_goals (
      simp -failIfUnchanged (disch := omega) only [parley_spelling, Int.reduceToNat]
        at h ⊢
      all_goals exact_mod_cast h)))

/-- `parley_instance_real e`: as `parley_instance`, the item stated in ℝ and
the step in ℚ. A rational statement cannot be found inside a real one, since
`norm_cast` lifts only to casts of integers; the step is lifted to ℝ instead
(`rify`), where the casts of both are pushed down to the letters, and the two
meet by moving their casts alike (`exact_mod_cast`): `rify` lifts a
comparison of integers too, `0 < N` as `(0 : ℝ) < ↑N`, which the item states
in ℤ. -/
macro "parley_instance_real " e:term:max : tactic =>
  `(tactic| (
    have h := $e:term
    rify
    push_cast at h ⊢
    exact_mod_cast h))

end
