module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialNonzero

theorem factorial_nonzero (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.factorial n : ℤ) ≠ 0 := by
  -- 1. mun:counting-factorial-nonzero
  have s1 : (LeanBridges.Counting.factorial n : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.FactorialNonzero
