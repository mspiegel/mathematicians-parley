module

public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Library

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseAll

theorem choose_all (N : ℕ) :
    (Parley.Library.choose (N : ℤ) (N : ℤ) : ℤ) = 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ (N : ℤ) := by parley_side
  have s1b : (N : ℤ) ≤ (N : ℤ) := by parley_side
  -- 2. def:range-between k := N, a := 0, b := N, from 1
  have s2 : (N : ℤ) ∈ Finset.Icc (0 : ℤ) (N : ℤ) := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ)))).mpr (by parley_side)
  -- 3. algebra
  have s3 : (N : ℤ) - (N : ℤ) = 0 := by parley_ring
  -- 4. calculation
  have s4 : (Parley.Library.factorial ((N : ℤ) - (N : ℤ)) : ℤ) = 1 := by
    calc (Parley.Library.factorial ((N : ℤ) - (N : ℤ)) : ℤ) = (Parley.Library.factorial (0 : ℤ) : ℤ) := by parley_subst s3
      _ = 1 := by norm_num
  -- 5. calculation
  have s5 : (Parley.Library.choose (N : ℤ) (N : ℤ) : ℤ) = 1 := by
    qify
    calc (Parley.Library.choose (N : ℤ) (N : ℤ) : ℚ) = (Parley.Library.factorial (N : ℤ) : ℚ) / ((Parley.Library.factorial ((N : ℤ) - (N : ℤ)) : ℚ) * (Parley.Library.factorial (N : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (k := (N : ℤ))) (by parley_side)).symm
      _ = (Parley.Library.factorial (N : ℤ) : ℚ) / (1 * (Parley.Library.factorial (N : ℤ) : ℚ)) := by
          have s4_w : (Parley.Library.factorial ((N : ℤ) - (N : ℤ)) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination h
          parley_subst s4_w
      _ = 1 := by parley_ring
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.ChooseAll
