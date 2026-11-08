module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-neither-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesNeitherFactor.DividesNeitherFactor

theorem divides_neither_factor (x : ℤ) (y : ℤ) (z : ℤ) (hH4 : x ≠ 0) (hH5 : ¬ x ∣ y * z) :
    (¬ x ∣ y ∧ ¬ x ∣ z) := by
  -- 1. contradiction
  have s1 : ¬ x ∣ y := by
    intro hS1
    -- 1.1. mun:divides-multiple e := x, a := y, x := z, from S1
    have s1_1 : x ∣ y * z := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := y) (x := z) hS1)
    -- 1.2. restate H5
    have s1_2 : ¬ x ∣ y * z := by parley_side
    exact s1_2 s1_1
  -- 2. contradiction
  have s2 : ¬ x ∣ z := by
    intro hS2
    -- 2.1. mun:divides-multiple e := x, a := z, x := y, from S2
    have s2_1 : x ∣ z * y := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := x) (a := z) (x := y) hS2)
    -- 2.2. substitute
    have s2_2 : x ∣ y * z := by
      have c1 : z * y = y * z := by parley_ring
      have row1 : x ∣ y * z := by parley_subst_at c1 s2_1
      exact row1
    -- 2.3. restate H5
    have s2_3 : ¬ x ∣ y * z := by parley_side
    exact s2_3 s2_2
  -- 3. join 1, 2
  have s3 : ¬ x ∣ y ∧ ¬ x ∣ z := by parley_side
  exact ⟨(s3).1, (s3).2⟩

end Parley.Proofs.Hammack.DividesNeitherFactor.DividesNeitherFactor
