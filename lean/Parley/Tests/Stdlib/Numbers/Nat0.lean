module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0

theorem nat0 (n : ℤ) (hH2 : 0 ≤ n) :
    (0 < n ∨ n = 0) := by
  -- 1. def:numbers-nat0, from H2
  have s1 : 0 < n ∨ n = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := n))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.Nat0
