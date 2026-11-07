module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsSquare

theorem abs_square (x : ℝ) :
    abs x ^ 2 = x ^ 2 := by
  -- 1. mun:numbers-abs-square
  have s1 : abs x ^ 2 = x ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_square (x := x))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsSquare
