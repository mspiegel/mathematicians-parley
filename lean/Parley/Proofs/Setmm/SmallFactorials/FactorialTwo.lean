module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

theorem factorial_two :
    (Parley.Library.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial n := 1
  have s1 : (Parley.Library.factorial (1 + 1 : ℤ) : ℤ) = (Parley.Library.factorial (1 : ℤ) : ℤ) * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 1))).symm
  -- 2. substitute
  have s2 : (Parley.Library.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by
    have c1 : (Parley.Library.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm
    have row1 : (Parley.Library.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (Parley.Library.factorial (2 : ℤ) : ℤ) = 1 * 2 := by
    have c1 : (1 + 1 : ℤ) = 2 := by parley_arith
    have row1 : (Parley.Library.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (Parley.Library.factorial (2 : ℤ) : ℤ) = 2 := by
    calc (Parley.Library.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialTwo
