module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0AsInt

theorem nat0_as_int (n : ℝ) :
    ((∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = n) ↔ (∃ m : ℤ, (m : ℝ) = n) ∧ 0 ≤ n) := by
  -- 1. mun:numbers-nat0-as-int
  have s1 : (∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = n) ↔ (∃ m : ℤ, (m : ℝ) = n) ∧ 0 ≤ n := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := n)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := n))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := n)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.Nat0AsInt
