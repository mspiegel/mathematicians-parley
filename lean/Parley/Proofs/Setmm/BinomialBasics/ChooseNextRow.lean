module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow

theorem choose_next_row (N : ℕ) :
    (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ (N : ℤ) := by parley_side
  have s1b : (N : ℤ) ≤ (N : ℤ) + 1 := by parley_side
  -- 2. def:range-between k := N, a := 0, b := N + 1, from 1
  have s2 : (N : ℤ) ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side); parley_side)
  -- 3. algebra
  have s3 : (N : ℤ) + 1 - (N : ℤ) = 1 := by parley_ring
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = 1 := by
    calc (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_subst s3
      _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
  -- 5. def:factorial n := N
  have s5 : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (N : ℤ) : ℤ) * ((N : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_side)
  -- 6. calculation
  have s6 : (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
    qify
    calc (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℚ) = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); parley_side)
      _ = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / (1 * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by
          have s4_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s4_w | parley_subst s4
      _ = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) / (1 * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by
          have s5_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s5; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s5_w | parley_subst s5
      _ = (N : ℚ) + 1 := by parley_ring
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow
