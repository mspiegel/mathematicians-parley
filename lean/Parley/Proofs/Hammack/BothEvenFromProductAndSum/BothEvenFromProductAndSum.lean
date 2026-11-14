module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/both-even-from-product-and-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BothEvenFromProductAndSum.BothEvenFromProductAndSum

theorem both_even_from_product_and_sum (a : ℤ) (b : ℤ) (hH3 : Even (a * b)) (hH4 : Even (a + b)) :
    (Even a ∧ Even b) := by
  -- 1. mun:even-product-factor, from H3
  have s1 : Even a ∨ Even b := by exact ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp hH3
  -- 2. obtain m: def:even n := a + b, from H4
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a + b))).mp hH4
  -- 3. cases, from 1
  have s3 : Even a ∧ Even b := by
    rcases s1 with hC1 | hC2
    · skip
      -- 3.1. obtain j: def:even, from C1
      obtain ⟨j, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp hC1
      -- 3.2. algebra, from 2, 3.1
      have s3_2 : b = 2 * (m - j) := by linear_combination s2 + (-1) * s3_1
      -- 3.3. def:even n := b, from 3.2
      have s3_3 : Even b := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mpr ⟨m - j, s3_2⟩
      -- 3.4. join C1, 3.3
      have s3_4 : Even a ∧ Even b := ⟨hC1, s3_3⟩
      exact ⟨(s3_4).1, (s3_4).2⟩
    · skip
      -- 3.5. obtain j: def:even, from C2
      obtain ⟨j, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp hC2
      -- 3.6. algebra, from 2, 3.5
      have s3_6 : a = 2 * (m - j) := by linear_combination s2 + (-1) * s3_5
      -- 3.7. def:even n := a, from 3.6
      have s3_7 : Even a := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mpr ⟨m - j, s3_6⟩
      -- 3.8. join C2, 3.7
      have s3_8 : Even a ∧ Even b := ⟨s3_7, hC2⟩
      exact ⟨(s3_8).1, (s3_8).2⟩
  exact ⟨(s3).1, (s3).2⟩

end Parley.Proofs.Hammack.BothEvenFromProductAndSum.BothEvenFromProductAndSum
