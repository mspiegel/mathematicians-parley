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

/-! Written from proofs/hammack/cubic-sum-even-iff-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicSumEvenIffEven.CubicSumEvenIffEven

theorem cubic_sum_even_iff_even (a : ℤ) :
    (Even (a ^ 3 + a ^ 2 + a) ↔ Even a) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. mun:even-or-odd n := a
    have s1 : Even a ∨ Odd a := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))
    -- 2. cases, from 1
    rcases s1 with hC1 | hC2
    · skip
      exact hC1
    · skip
      -- 2.1. obtain k: def:odd, from C2
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp hC2
      -- 2.2. algebra, from 2.1
      have s2_2 : a ^ 3 + a ^ 2 + a = 2 * (4 * k ^ 3 + 8 * k ^ 2 + 6 * k + 1) + 1 := by linear_combination (norm := parley_norm) (2 * a * k + a ^ 2 + 4 * k ^ 2 + 2 * a + 6 * k + 3) * s2_1
      -- 2.3. def:odd n := a³ + a² + a, from 2.2
      have s2_3 : Odd (a ^ 3 + a ^ 2 + a) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 8 * k ^ 2 + 6 * k + 1, s2_2⟩
      -- 2.4. mun:not-both n := a³ + a² + a, from D1
      have s2_4 : ¬ Odd (a ^ 3 + a ^ 2 + a) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := a ^ 3 + a ^ 2 + a) hD1)
      exact absurd s2_3 s2_4
  · skip
    intro hD2
    -- 3. obtain k: def:even, from D2
    obtain ⟨k, s3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp hD2
    -- 4. algebra, from 3
    have s4 : a ^ 3 + a ^ 2 + a = 2 * (4 * k ^ 3 + 2 * k ^ 2 + k) := by linear_combination (norm := parley_norm) (2 * a * k + a ^ 2 + 4 * k ^ 2 + a + 2 * k + 1) * s3
    -- 5. def:even n := a³ + a² + a, from 4
    exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 3 + a ^ 2 + a))).mpr ⟨4 * k ^ 3 + 2 * k ^ 2 + k, s4⟩

end Parley.Proofs.Hammack.CubicSumEvenIffEven.CubicSumEvenIffEven
