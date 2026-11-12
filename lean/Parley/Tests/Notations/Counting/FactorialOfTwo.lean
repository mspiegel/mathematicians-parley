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

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfTwo

theorem factorial_of_two :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial
  have s1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
  -- 2. def:factorial n := 1
  have s2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by norm_num))
  -- 3. substitute 1! = 1 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = t * (1 + 1))) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = 1 * t)) s4 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. calculation
  calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by exact s5
    _ = 2 := by norm_num

end Parley.Tests.Notations.Counting.FactorialOfTwo
