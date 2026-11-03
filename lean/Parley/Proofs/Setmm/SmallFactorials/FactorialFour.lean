module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.SmallFactorials.FactorialThree

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialFour

theorem factorial_four :
    (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
  -- 1. def:factorial n := 3
  have s1 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) * (3 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); parley_side)
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by first | linear_combination (norm := parley_norm) Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three | exact_mod_cast (Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three).symm | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; parley_int_power h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialThree.factorial_three; parley_side)
    have row1 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by
    have c1 : (3 + 1 : ℤ) = 4 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
    calc (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by parley_side
      _ = 24 := by norm_num
  all_goals exact s4

end Parley.Proofs.Setmm.SmallFactorials.FactorialFour
