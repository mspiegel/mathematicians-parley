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
public import Parley.Proofs.Setmm.SmallFactorials.FactorialThree

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialFour

theorem factorial_four :
    (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
  -- 1. def:factorial n := 3
  have s1 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) * (3 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (3 : ℤ)) (by norm_num))
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by exact Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three
    have row1 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = t * (3 + 1))) c1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by
    have c1 : (3 + 1 : ℤ) = 4 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ) = 6 * t)) c1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 4. calculation
  calc (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by exact s3
    _ = 24 := by norm_num

end Parley.Proofs.Setmm.SmallFactorials.FactorialFour
