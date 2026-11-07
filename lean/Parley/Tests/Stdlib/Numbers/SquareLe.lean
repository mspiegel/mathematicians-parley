module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.SquareLe

theorem square_le (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y ≥ 0) :
    (x ≤ y ↔ x ^ 2 ≤ y ^ 2) := by
  -- 1. mun:numbers-square-le, from H3, H4
  have s1 : x ≤ y ↔ x ^ 2 ≤ y ^ 2 := by first | exact (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.SquareLe
