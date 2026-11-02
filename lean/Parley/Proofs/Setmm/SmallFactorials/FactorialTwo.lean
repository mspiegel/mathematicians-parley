module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

theorem factorial_two :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial n := 1
  have s1 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_side)
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
    have row1 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
    have c1 : (1 + 1 : ℤ) = 2 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
    calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialTwo
