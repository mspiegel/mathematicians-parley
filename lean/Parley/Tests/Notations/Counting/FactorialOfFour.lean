module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfFour

theorem factorial_of_four :
    (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
  -- 1. thm:factorial-of-two
  have s1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by exact Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two
  -- 2. def:factorial n := 2
  have s2 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) * (2 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by norm_num))
  -- 3. substitute 2! = 2 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = t * (2 + 1))) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. arithmetic
  have s4 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 5. substitute 2 + 1 = 3 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = 2 * t)) s4 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. calculation
  have s6 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
    calc (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := s5
      _ = 6 := by norm_num
  -- 7. def:factorial n := 3
  have s7 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) * (3 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (3 : ℤ)) (by norm_num))
  -- 8. substitute 3! = 6 (line 6) into line 7
  have s8 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = t * (3 + 1))) s6 s7; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 9. arithmetic
  have s9 : (3 + 1 : ℤ) = 4 := by parley_arith
  -- 10. substitute 3 + 1 = 4 (line 9) into line 8
  have s10 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = 6 * t)) s9 s8; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 11. calculation
  calc (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := s10
    _ = 24 := by norm_num

end Parley.Tests.Notations.Counting.FactorialOfFour
