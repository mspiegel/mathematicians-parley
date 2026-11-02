module

public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Library

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow

theorem choose_next_row (N : ℕ) :
    (Parley.Library.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ (N : ℤ) := by parley_side
  have s1b : (N : ℤ) ≤ (N : ℤ) + 1 := by parley_side
  -- 2. def:range-between k := N, a := 0, b := N + 1, from 1
  have s2 : (N : ℤ) ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side)
  -- 3. algebra
  have s3 : (N : ℤ) + 1 - (N : ℤ) = 1 := by parley_ring
  -- 4. calculation
  have s4 : (Parley.Library.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = 1 := by
    calc (Parley.Library.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = (Parley.Library.factorial (1 : ℤ) : ℤ) := by parley_subst s3
      _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm
  -- 5. def:factorial n := N
  have s5 : (Parley.Library.factorial ((N : ℤ) + 1) : ℤ) = (Parley.Library.factorial (N : ℤ) : ℤ) * ((N : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N))).symm
  -- 6. calculation
  have s6 : (Parley.Library.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
    qify
    calc (Parley.Library.choose ((N : ℤ) + 1) (N : ℤ) : ℚ) = (Parley.Library.factorial ((N : ℤ) + 1) : ℚ) / ((Parley.Library.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) * (Parley.Library.factorial (N : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side)).symm
      _ = (Parley.Library.factorial ((N : ℤ) + 1) : ℚ) / (1 * (Parley.Library.factorial (N : ℤ) : ℚ)) := by
          have s4_w : (Parley.Library.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination h
          parley_subst s4_w
      _ = (Parley.Library.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) / (1 * (Parley.Library.factorial (N : ℤ) : ℚ)) := by
          have s5_w : (Parley.Library.factorial ((N : ℤ) + 1) : ℚ) = (Parley.Library.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s5; push_cast at h; linear_combination h
          parley_subst s5_w
      _ = (N : ℚ) + 1 := by parley_ring
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow
