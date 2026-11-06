module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/hammack/square-from-choose.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareFromChoose.ChooseOne

set_option maxHeartbeats 400000 in
theorem choose_one (n : ℤ) (hH1 : 0 < n) :
    (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) = k := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. thm:pascal n := 0, k := 1
      have s1_1 : (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (0 : ℤ) (1 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))); parley_side)
      -- 1.2. substitute
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) := by
        have c1 : (1 - 1 : ℤ) = 0 := by parley_arith
        have row1 : (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst_at c1 s1_1
        exact row1
      -- 1.3. arithmetic
      have s1_3 : (0 : ℤ) < 1 := by parley_arith
      -- 1.4. def:C n := 0, k := 1, from 1.3
      have s1_4 : (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) (by parley_side); parley_side)
      -- 1.5. mun:binomial-zero-index n := 0
      have s1_5 : (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side)); parley_side)
      -- 1.6. algebra, from 1.2, 1.4, 1.5
      have s1_6 : (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) = 1 := by linear_combination (norm := parley_norm) (-1) * s1_2 + s1_4 + s1_5
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.7. thm:pascal n := k, k := 1
      have s1_7 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose k (1 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (by parley_side) (k := (1 : ℤ))); parley_side)
      -- 1.8. substitute 1 − 1 = 0 (arithmetic) into line 1.7
      have s1_8 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose k (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by parley_subst_at (show (1 - 1 : ℤ) = 0 by parley_side) s1_7
      -- 1.9. mun:binomial-zero-index n := k
      have s1_9 : (LeanBridges.Counting.choose k (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) (by parley_side)); parley_side)
      -- 1.10. algebra, from IH, 1.8, 1.9
      have s1_10 : (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) = k + 1 := by linear_combination (norm := parley_norm) hIH + (-1) * s1_8 + s1_9
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SquareFromChoose.ChooseOne
