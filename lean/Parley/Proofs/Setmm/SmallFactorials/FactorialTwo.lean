module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

theorem factorial_two :
    (Nat.factorial 2 : ℤ) = 2 := by
  -- 1. def:factorial n := 1
  have s1 : (Nat.factorial (1 + 1) : ℤ) = (Nat.factorial 1 : ℤ) * (1 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))
  -- 2. substitute
  have s2 : (Nat.factorial (1 + 1) : ℤ) = 1 * (1 + 1) := by
    have c1 : (Nat.factorial 1 : ℤ) = 1 := by linear_combination Parley.Items.Stdlib.Counting.def_factorial_2
    have row1 : (Nat.factorial (1 + 1) : ℤ) = 1 * (1 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (Nat.factorial 2 : ℤ) = 1 * 2 := by
    have c1 : (1 + 1 : ℤ) = 2 := by parley_arith
    have row1 : (Nat.factorial 2 : ℤ) = 1 * 2 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (Nat.factorial 2 : ℤ) = 2 := by
    calc (Nat.factorial 2 : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialTwo
