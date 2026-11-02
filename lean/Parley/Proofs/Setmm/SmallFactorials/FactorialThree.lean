module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialThree

theorem factorial_three :
    (Parley.Library.factorial (3 : ℤ) : ℤ) = 6 := by
  -- 1. def:factorial n := 2
  have s1 : (Parley.Library.factorial (2 + 1 : ℤ) : ℤ) = (Parley.Library.factorial (2 : ℤ) : ℤ) * (2 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := 2)); qify; linear_combination (norm := parley_norm) h)
  -- 2. substitute
  have s2 : (Parley.Library.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by
    have c1 : (Parley.Library.factorial (2 : ℤ) : ℤ) = 2 := by first | linear_combination (norm := parley_norm) Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two | exact_mod_cast (Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two).symm | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; qify; linear_combination (norm := parley_norm) h)
    have row1 : (Parley.Library.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (Parley.Library.factorial (3 : ℤ) : ℤ) = 2 * 3 := by
    have c1 : (2 + 1 : ℤ) = 3 := by parley_arith
    have row1 : (Parley.Library.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (Parley.Library.factorial (3 : ℤ) : ℤ) = 6 := by
    calc (Parley.Library.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  all_goals parley_side

end Parley.Proofs.Setmm.SmallFactorials.FactorialThree
