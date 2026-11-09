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
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfFour

set_option maxHeartbeats 400000 in
theorem factorial_of_four :
    (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
  -- 1. thm:factorial-of-two
  have s1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by exact Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two
  -- 2. def:factorial n := 2
  have s2 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) * (2 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side))
  -- 3. substitute 2! = 2 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by first | parley_subst_at s1 s2 | (have e_nat : LeanBridges.Counting.factorial (2 : ℤ) = 2 := by exact_mod_cast s1; parley_subst_at e_nat s2)
  -- 4. arithmetic
  have s4 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 5. substitute 2 + 1 = 3 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by first | parley_subst_at s4 s3 | (have e_nat : 2 + 1 = 3 := by exact_mod_cast s4; parley_subst_at e_nat s3)
  -- 6. calculation
  have s6 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
    calc (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  -- 7. def:factorial n := 3
  have s7 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) * (3 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (3 : ℤ)) (by parley_side))
  -- 8. substitute 3! = 6 (line 6) into line 7
  have s8 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by first | parley_subst_at s6 s7 | (have e_nat : LeanBridges.Counting.factorial (3 : ℤ) = 6 := by exact_mod_cast s6; parley_subst_at e_nat s7)
  -- 9. arithmetic
  have s9 : (3 + 1 : ℤ) = 4 := by parley_arith
  -- 10. substitute 3 + 1 = 4 (line 9) into line 8
  have s10 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by first | parley_subst_at s9 s8 | (have e_nat : 3 + 1 = 4 := by exact_mod_cast s9; parley_subst_at e_nat s8)
  -- 11. calculation
  calc (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by parley_side
    _ = 24 := by norm_num

end Parley.Tests.Notations.Counting.FactorialOfFour
