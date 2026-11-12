module

public import AlgebraTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/positive-rational-fraction.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PositiveRationalFraction.PositiveRationalFraction

theorem positive_rational_fraction (A : ℝ) (hH2 : ∃ m : ℚ, (m : ℝ) = A) (hH3 : 0 < A) :
    (∃ x : ℤ, 0 < x ∧ (∃ y : ℤ, 0 < y ∧ A = (x : ℝ) / (y : ℝ))) := by
  -- 1. obtain p, q: def:rational x := A, from H2
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp hH2
  -- 2. contradiction
  have s2 : 0 < p := by
    by_contra hS
    -- 2.1. inequalities, from S
    have s2_1 : p ≤ 0 := by linarith only [hS]
    -- 2.2. mun:divide-le x := p, y := 0, c := q, from 2.1
    have r24_1 : q > 0 := by linarith only [s1a]
    have s2_2 : (p : ℚ) / (q : ℚ) ≤ 0 / (q : ℚ) := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (p : ℚ)) (y := (0 : ℚ)) (c := (q : ℚ)) (by exact_mod_cast s2_1) (by exact_mod_cast gt_iff_lt.mp r24_1))
    -- 2.3. calculation
    have s2_3 : A ≤ 0 := by
      calc A = (p : ℝ) / (q : ℝ) := by exact s1b
        _ ≤ 0 / (q : ℝ) := by parley_side
        _ = 0 := by parley_ring
    -- 2.4. inequalities, from H3
    have s2_4 : ¬ A ≤ 0 := by linarith only [hH3]
    exact s2_4 s2_3
  -- 3. mun:pos-int-nat m := p, from 2
  have s3 : 0 < p := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2)
  -- 4. exhibit, from 1, 3
  exact ⟨p, s3, q, s1a, s1b⟩

end Parley.Proofs.Setmm.PositiveRationalFraction.PositiveRationalFraction
