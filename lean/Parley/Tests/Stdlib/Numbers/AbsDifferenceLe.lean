module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsDifferenceLe

theorem abs_difference_le (y : ℝ) (b : ℝ) (e : ℝ) :
    (abs (y - b) ≤ e ↔ b - e ≤ y ∧ y ≤ b + e) := by
  -- 1. mun:numbers-abs-difference-le x := y, c := b, δ := e
  have s1 : abs (y - b) ≤ e ↔ b - e ≤ y ∧ y ≤ b + e := by first | exact (Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := y) (c := b) (δ := e)) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := y) (c := b) (δ := e))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := y) (c := b) (δ := e)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := y) (c := b) (δ := e)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := y) (c := b) (δ := e)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsDifferenceLe
