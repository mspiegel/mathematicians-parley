module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfTwo

theorem factorial_of_two :
    (Nat.factorial 2 : ℤ) = 2 := by
  -- 1. def:factorial
  have s1 : (Nat.factorial 1 : ℤ) = 1 := by linear_combination Parley.Items.Stdlib.Counting.def_factorial_2
  -- 2. def:factorial n := 1
  have s2 : (Nat.factorial (1 + 1) : ℤ) = (Nat.factorial 1 : ℤ) * (1 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))
  -- 3. substitute 1! = 1 (line 1) into line 2
  have s3 : (Nat.factorial (1 + 1) : ℤ) = 1 * (1 + 1) := by parley_subst_at s1 s2
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 3
  have s5 : (Nat.factorial 2 : ℤ) = 1 * 2 := by parley_subst_at s4 s3
  -- 6. calculation
  have s6 : (Nat.factorial 2 : ℤ) = 2 := by
    calc (Nat.factorial 2 : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals parley_side

end Parley.Tests.Notations.Counting.FactorialOfTwo
