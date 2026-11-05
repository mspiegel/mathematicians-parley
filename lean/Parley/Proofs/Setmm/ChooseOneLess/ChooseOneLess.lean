module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/choose-one-less.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseOneLess.ChooseOneLess

theorem choose_one_less (N : ℕ) :
    (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ (N : ℤ) = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side); parley_side)
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. inequalities, from H1
      have s2_1a : 0 ≤ (N : ℤ) := by parley_order
      have s2_1b : (N : ℤ) ≤ (N : ℤ) + 1 := by parley_order
      -- 2.2. def:range-between k := N, a := 0, b := N + 1, from 2.1
      have s2_2 : (N : ℤ) ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := (N : ℤ)) (a := (0 : ℤ)) (b := (N : ℤ) + 1))).mpr (by parley_side); parley_side)
      -- 2.3. algebra
      have s2_3 : (N : ℤ) + 1 - (N : ℤ) = 1 := by parley_ring
      -- 2.4. calculation
      have s2_4 : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = 1 := by
        calc (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_subst s2_3
          _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
      -- 2.5. def:factorial n := N
      have s2_5 : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (N : ℤ) : ℤ) * ((N : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N)); parley_side)
      -- 2.6. calculation
      have s2_6 : (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
        qify
        calc (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℚ) = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / ((LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (k := (N : ℤ))) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) / (1 * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by
              have s2_4_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1 - (N : ℤ)) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_4_w | parley_subst s2_4
          _ = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) / (1 * (LeanBridges.Counting.factorial (N : ℤ) : ℚ)) := by
              have s2_5_w : (LeanBridges.Counting.factorial ((N : ℤ) + 1) : ℚ) = (LeanBridges.Counting.factorial (N : ℤ) : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = (N : ℚ) + 1 := by parley_ring
      all_goals parley_side
    · skip
      -- 2.7. algebra, from C2
      have s2_7 : (N : ℤ) + 1 = 1 := by linear_combination (norm := parley_norm) hC2
      -- 2.8. calculation
      have s2_8 : (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (N : ℤ) + 1 := by
        calc (LeanBridges.Counting.choose ((N : ℤ) + 1) (N : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 : ℤ) (N : ℤ) : ℤ) := by parley_subst s2_7
          _ = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) := by parley_subst hC2
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); parley_side)
          _ = (N : ℤ) + 1 := by parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.ChooseOneLess.ChooseOneLess
