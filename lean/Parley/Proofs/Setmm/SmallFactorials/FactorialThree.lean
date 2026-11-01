module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialThree

theorem factorial_three :
    (Nat.factorial 3 : ℤ) = 6 := by
  -- 1. def:factorial n := 2
  have s1 : (Nat.factorial (2 + 1) : ℤ) = (Nat.factorial 2 : ℤ) * (2 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2))
  -- 2. substitute
  have s2 : (Nat.factorial (2 + 1) : ℤ) = 2 * (2 + 1) := by
    have c1 : (Nat.factorial 2 : ℤ) = 2 := by linear_combination Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two
    have row1 : (Nat.factorial (2 + 1) : ℤ) = 2 * (2 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (Nat.factorial 3 : ℤ) = 2 * 3 := by
    have c1 : (2 + 1 : ℤ) = 3 := by parley_arith
    have row1 : (Nat.factorial 3 : ℤ) = 2 * 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (Nat.factorial 3 : ℤ) = 6 := by
    calc (Nat.factorial 3 : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialThree
