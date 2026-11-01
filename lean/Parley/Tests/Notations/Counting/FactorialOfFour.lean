module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfFour

theorem factorial_of_four :
    (Nat.factorial 4 : ℤ) = 24 := by
  -- 1. thm:factorial-of-two
  have s1 : (Nat.factorial 2 : ℤ) = 2 := by linear_combination Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two
  -- 2. def:factorial n := 2
  have s2 : (Nat.factorial (2 + 1) : ℤ) = (Nat.factorial 2 : ℤ) * (2 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2))
  -- 3. substitute 2! = 2 (line 1) into line 2
  have s3 : (Nat.factorial (2 + 1) : ℤ) = 2 * (2 + 1) := by parley_subst_at s1 s2
  -- 4. arithmetic
  have s4 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 5. substitute 2 + 1 = 3 (line 4) into line 3
  have s5 : (Nat.factorial 3 : ℤ) = 2 * 3 := by parley_subst_at s4 s3
  -- 6. calculation
  have s6 : (Nat.factorial 3 : ℤ) = 6 := by
    calc (Nat.factorial 3 : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  -- 7. def:factorial n := 3
  have s7 : (Nat.factorial (3 + 1) : ℤ) = (Nat.factorial 3 : ℤ) * (3 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3))
  -- 8. substitute 3! = 6 (line 6) into line 7
  have s8 : (Nat.factorial (3 + 1) : ℤ) = 6 * (3 + 1) := by parley_subst_at s6 s7
  -- 9. arithmetic
  have s9 : (3 + 1 : ℤ) = 4 := by parley_arith
  -- 10. substitute 3 + 1 = 4 (line 9) into line 8
  have s10 : (Nat.factorial 4 : ℤ) = 6 * 4 := by parley_subst_at s9 s8
  -- 11. calculation
  have s11 : (Nat.factorial 4 : ℤ) = 24 := by
    calc (Nat.factorial 4 : ℤ) = 6 * 4 := by parley_side
      _ = 24 := by norm_num
  all_goals parley_side

end Parley.Tests.Notations.Counting.FactorialOfFour
