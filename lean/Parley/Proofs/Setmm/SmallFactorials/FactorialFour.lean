module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Setmm.SmallFactorials.FactorialThree

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialFour

theorem factorial_four :
    (Nat.factorial 4 : ℤ) = 24 := by
  -- 1. def:factorial n := 3
  have s1 : (Nat.factorial (3 + 1) : ℤ) = (Nat.factorial 3 : ℤ) * (3 + 1) := by linear_combination (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3))
  -- 2. substitute
  have s2 : (Nat.factorial (3 + 1) : ℤ) = 6 * (3 + 1) := by
    have c1 : (Nat.factorial 3 : ℤ) = 6 := by linear_combination Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three
    have row1 : (Nat.factorial (3 + 1) : ℤ) = 6 * (3 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (Nat.factorial 4 : ℤ) = 6 * 4 := by
    have c1 : (3 + 1 : ℤ) = 4 := by parley_arith
    have row1 : (Nat.factorial 4 : ℤ) = 6 * 4 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (Nat.factorial 4 : ℤ) = 24 := by
    calc (Nat.factorial 4 : ℤ) = 6 * 4 := by parley_side
      _ = 24 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialFour
