module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-root-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareRootByAlgebra.ARootHalvedByInequalities

theorem a_root_halved_by_inequalities :
    0 ≤ Real.sqrt (2 : ℝ) / 2 := by
  -- 1. def:sqrt x := 2
  have r34_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (2 : ℝ) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); parley_side)
  have s1b : Real.sqrt (2 : ℝ) ^ 2 = 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_side)
  -- 2. inequalities
  have s2 : 0 ≤ Real.sqrt (2 : ℝ) / 2 := by parley_order
  all_goals exact s2

end Parley.Tests.Elaborator.ASquareRootByAlgebra.ARootHalvedByInequalities
