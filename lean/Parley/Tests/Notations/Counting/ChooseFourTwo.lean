module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Tests.Notations.Counting.FactorialOfFour
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ChooseFourTwo

theorem choose_four_two :
    (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℤ) = 6 := by
  -- 1. thm:factorial-of-four
  have s1 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four | exact_mod_cast (Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four).symm | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; parley_int_power h) | (have h := Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four; parley_side)
  -- 2. thm:factorial-of-two
  have s2 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two | exact_mod_cast (Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two).symm | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; parley_int_power h) | (have h := Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two; parley_side)
  -- 3. def:C n := 4, k := 2
  have r89_1 : (0 : ℤ) ≤ 2 := by parley_arith
  have r89_2 : (2 : ℤ) ≤ 4 := by parley_arith
  have r89_3 : (2 : ℤ) ∈ Finset.Icc (0 : ℤ) (4 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := (4 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := (4 : ℤ)))).mpr (by parley_side); parley_side)
  have s3 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) / ((LeanBridges.Counting.factorial (4 - 2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := 4) (k := (2 : ℤ))) (by parley_side); parley_side)
  -- 4. arithmetic
  have s4 : (4 - 2 : ℤ) = 2 := by parley_arith
  -- 5. substitute 4 − 2 = 2 (line 4) into line 3
  have s5 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) / ((LeanBridges.Counting.factorial (2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by
    have s4_w : (4 - 2 : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst_at s4_w s3 | parley_subst_at s4 s3
  -- 6. substitute 4! = 24 (line 1) into line 5
  have s6 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / ((LeanBridges.Counting.factorial (2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by
    have s1_w : (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) = 24 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst_at s1_w s5 | parley_subst_at s1 s5
  -- 7. substitute 2! = 2 (line 2) into line 6
  have s7 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / (2 * 2) := by
    have s2_w : (LeanBridges.Counting.factorial (2 : ℤ) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst_at s2_w s6 | parley_subst_at s2 s6
  -- 8. calculation
  have s8 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℤ) = 6 := by
    qify
    calc (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / (2 * 2) := by parley_side
      _ = 6 := by norm_num
  all_goals parley_side

end Parley.Tests.Notations.Counting.ChooseFourTwo
