module

public import NormTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-root-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootPositive.SquareRootPositive

theorem square_root_positive (a : ℝ) (hH2 : 0 < a) :
    0 < Real.sqrt a := by
  -- 1. def:sqrt x := a
  have r10_1 : 0 ≤ a := by parley_side
  have s1a : Real.sqrt a ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) r10_1)
  have s1b : Real.sqrt a ^ 2 = a := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) r10_1)
  -- 2. contradiction
  by_contra hS
  -- 2.1. inequalities, from S
  have s2_1 : Real.sqrt a ≤ 0 := by parley_order
  -- 2.2. inequalities, from 1
  have s2_2 : Real.sqrt a ≥ 0 := by parley_order
  -- 2.3. antisymmetry, from 2.1, 2.2
  have s2_3 : Real.sqrt a = 0 := by parley_side
  -- 2.4. algebra, from 2.3
  have s2_4 : Real.sqrt a ^ 2 = 0 := by linear_combination (norm := parley_norm) (Real.sqrt a) * s2_3
  -- 2.5. transitivity, from 1, 2.4
  have s2_5 : a = 0 := by parley_side
  -- 2.6. inequalities
  have s2_6 : a ≤ 0 := by parley_order
  -- 2.7. inequalities, from 2.6
  have s2_7 : ¬ 0 < a := by parley_side
  exact s2_7 hH2

end Parley.Proofs.Setmm.SquareRootPositive.SquareRootPositive
