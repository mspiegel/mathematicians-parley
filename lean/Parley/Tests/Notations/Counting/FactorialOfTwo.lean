module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfTwo

theorem factorial_of_two :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial
  have s1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
  -- 2. def:factorial n := 1
  have s2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); parley_side)
  -- 3. substitute 1! = 1 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by parley_subst_at s1 s2
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at s4 s3
  -- 6. calculation
  have s6 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
    calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals parley_side

end Parley.Tests.Notations.Counting.FactorialOfTwo
