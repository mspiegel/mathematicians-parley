module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/positive-number-with-square-below-root.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PositiveNumberWithSquareBelowRoot.PositiveNumberWithSquareBelowRoot

theorem positive_number_with_square_below_root :
    (∃ x : ℝ, x > 0 ∧ x ^ 2 < Real.sqrt x) := by
  -- 1. def:sqrt x := 1/4
  have r10_1 : (1 / 4 : ℚ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (1 / 4 : ℝ) ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (1 / 4 : ℝ)) (by parley_side))
  have s1b : Real.sqrt (1 / 4 : ℝ) ^ 2 = 1 / 4 := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (1 / 4 : ℝ)) (by parley_side))
  -- 2. arithmetic
  have s2 : ((1 / 16) ^ 2 : ℚ) < 1 / 4 := by parley_arith
  -- 3. substitute (√(1/4))² = 1/4 (line 1) into line 2
  have s3 : (1 / 16) ^ 2 < Real.sqrt (1 / 4 : ℝ) ^ 2 := by parley_subst_at s1b s2
  -- 4. mun:square-less x := 1/16, y := √(1/4), from 1, 3
  have r20_1 : (1 / 16 : ℚ) ≥ 0 := by parley_arith
  have s4 : 1 / 16 < Real.sqrt (1 / 4 : ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (1 / 16 : ℝ)) (y := Real.sqrt (1 / 4 : ℝ)) (by parley_side) (by parley_side))).mpr s3 | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (1 / 16 : ℝ)) (y := Real.sqrt (1 / 4 : ℝ)) (by parley_side) (by parley_side))).mpr s3; parley_side)
  -- 5. substitute 1/16 = (1/4)² (arithmetic) into line 4
  have s5 : (1 / 4) ^ 2 < Real.sqrt (1 / 4 : ℝ) := by parley_subst_at (show (1 / 16 : ℝ) = (1 / 4) ^ 2 by parley_side) s4
  -- 6. arithmetic
  have s6 : (1 / 4 : ℚ) > 0 := by parley_arith
  -- 7. exhibit, from 5, 6
  exact ⟨(1 / 4 : ℝ), ⟨by parley_side, s5⟩⟩

end Parley.Proofs.Hammack.PositiveNumberWithSquareBelowRoot.PositiveNumberWithSquareBelowRoot
