module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfFour

theorem factorial_of_four :
    (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
  -- 1. thm:factorial-of-two
  have s1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two | exact_mod_cast (Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two).symm | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; parley_int_power h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; parley_side)
  -- 2. def:factorial n := 2
  have s2 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) * (2 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); parley_side)
  -- 3. substitute 2! = 2 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by parley_subst_at s1 s2
  -- 4. arithmetic
  have s4 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 5. substitute 2 + 1 = 3 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_subst_at s4 s3
  -- 6. calculation
  have s6 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
    calc (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  -- 7. def:factorial n := 3
  have s7 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) * (3 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 3)); parley_side)
  -- 8. substitute 3! = 6 (line 6) into line 7
  have s8 : (LeanBridges.Counting.factorial (3 + 1 : ℤ) : ℤ) = 6 * (3 + 1) := by parley_subst_at s6 s7
  -- 9. arithmetic
  have s9 : (3 + 1 : ℤ) = 4 := by parley_arith
  -- 10. substitute 3 + 1 = 4 (line 9) into line 8
  have s10 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by parley_subst_at s9 s8
  -- 11. calculation
  have s11 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by
    calc (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 6 * 4 := by parley_side
      _ = 24 := by norm_num
  all_goals exact s11

end Parley.Tests.Notations.Counting.FactorialOfFour
