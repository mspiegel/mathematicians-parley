module

public import ArithTactics
public import Counting
public import FactorialTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

theorem factorial_two :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial n := 1
  have s1 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side))
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
    have row1 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
    have c1 : (1 + 1 : ℤ) = 2 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by exact s3
    _ = 2 := by norm_num

end Parley.Proofs.Setmm.SmallFactorials.FactorialTwo
