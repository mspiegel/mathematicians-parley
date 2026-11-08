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
public import Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialThree

theorem factorial_three :
    (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
  -- 1. def:factorial n := 2
  have s1 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) * (2 + 1) := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side))
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by exact Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two
    have row1 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by
    have c1 : (2 + 1 : ℤ) = 3 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  calc (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_side
    _ = 6 := by norm_num

end Parley.Proofs.Setmm.SmallFactorials.FactorialThree
