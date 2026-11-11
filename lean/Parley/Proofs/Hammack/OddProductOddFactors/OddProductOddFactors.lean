module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-product-odd-factors.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddProductOddFactors.OddProductOddFactors

theorem odd_product_odd_factors (a : ℤ) (b : ℤ) (hH3 : Odd (a ^ 2 * (b ^ 2 - 2 * b))) :
    (Odd a ∧ Odd b) := by
  -- 1. mun:even-or-odd n := a
  have s1 : Even a ∨ Odd a := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))
  -- 2. cases, from 1
  have s2 : Odd a := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain m: def:even n := a, from C1
      obtain ⟨m, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp hC1
      -- 2.2. algebra, from 2.1
      have s2_2 : a ^ 2 * (b ^ 2 - 2 * b) = 2 * (2 * m ^ 2 * (b ^ 2 - 2 * b)) := by linear_combination (norm := parley_norm) (a * b ^ 2 + 2 * b ^ 2 * m - 2 * a * b - 4 * b * m) * s2_1
      -- 2.3. def:even n := a²·(b² − 2b), from 2.2
      have s2_3 : Even (a ^ 2 * (b ^ 2 - 2 * b)) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨2 * m ^ 2 * (b ^ 2 - 2 * b), s2_2⟩
      -- 2.4. mun:not-both n := a²·(b² − 2b), from 2.3
      have s2_4 : ¬ Odd (a ^ 2 * (b ^ 2 - 2 * b)) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s2_3)
      exact absurd hH3 s2_4
    · skip
      exact hC2
  -- 3. mun:even-or-odd n := b
  have s3 : Even b ∨ Odd b := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))
  -- 4. cases, from 3
  have s4 : Odd b := by
    rcases s3 with hC3 | hC4
    · skip
      -- 4.1. obtain m: def:even n := b, from C3
      obtain ⟨m, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp hC3
      -- 4.2. algebra, from 4.1
      have s4_2 : a ^ 2 * (b ^ 2 - 2 * b) = 2 * (a ^ 2 * (2 * m ^ 2 - 2 * m)) := by linear_combination (norm := parley_norm) (a ^ 2 * b + 2 * a ^ 2 * m - 2 * a ^ 2) * s4_1
      -- 4.3. def:even n := a²·(b² − 2b), from 4.2
      have s4_3 : Even (a ^ 2 * (b ^ 2 - 2 * b)) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2 * (b ^ 2 - 2 * b)))).mpr ⟨a ^ 2 * (2 * m ^ 2 - 2 * m), s4_2⟩
      -- 4.4. mun:not-both n := a²·(b² − 2b), from 4.3
      have s4_4 : ¬ Odd (a ^ 2 * (b ^ 2 - 2 * b)) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 2 * (b ^ 2 - 2 * b)) s4_3)
      exact absurd hH3 s4_4
    · skip
      exact hC4
  -- 5. join 2, 4
  have s5 : Odd a ∧ Odd b := by parley_side
  exact ⟨(s5).1, (s5).2⟩

end Parley.Proofs.Hammack.OddProductOddFactors.OddProductOddFactors
