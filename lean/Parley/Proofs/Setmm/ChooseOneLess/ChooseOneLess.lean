module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/choose-one-less.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseOneLess.ChooseOneLess

theorem choose_one_less (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side); parley_side)
  -- 2. cases, from 1
  have s2 : (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. inequalities, from H1
      have s2_1a : 0 ≤ N := by parley_order
      have s2_1b : N ≤ N + 1 := by parley_order
      -- 2.2. def:range-between k := N, a := 0, b := N + 1, from 2.1
      have s2_2 : N ∈ Finset.Icc (0 : ℤ) (N + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N + 1))).mpr (by parley_side); parley_side)
      -- 2.3. algebra
      have s2_3 : N + 1 - N = 1 := by parley_ring
      -- 2.4. calculation
      have s2_4 : (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = 1 := by
        calc (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_subst s2_3
          _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
      -- 2.5. def:factorial n := N
      have s2_5 : (LeanBridges.Counting.factorial (N + 1) : ℤ) = (LeanBridges.Counting.factorial N : ℤ) * (N + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); parley_side)
      -- 2.6. calculation
      have s2_6 : (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
        try qify
        calc (LeanBridges.Counting.choose (N + 1) N : ℚ) = (LeanBridges.Counting.factorial (N + 1) : ℚ) / ((LeanBridges.Counting.factorial (N + 1 - N) : ℚ) * (LeanBridges.Counting.factorial N : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.factorial (N + 1) : ℚ) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
              have s2_4_w : (LeanBridges.Counting.factorial (N + 1 - N) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_4_w | parley_subst s2_4
          _ = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
              have s2_5_w : (LeanBridges.Counting.factorial (N + 1) : ℚ) = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = (N : ℚ) + 1 := by parley_ring
      all_goals parley_side
    · skip
      -- 2.7. algebra, from C2
      have s2_7 : N + 1 = 1 := by linear_combination (norm := parley_norm) hC2
      -- 2.8. calculation
      have s2_8 : (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
        calc (LeanBridges.Counting.choose (N + 1) N : ℤ) = (LeanBridges.Counting.choose (1 : ℤ) N : ℤ) := by parley_subst s2_7
          _ = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) := by parley_subst hC2
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side)); parley_side)
          _ = N + 1 := by parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.ChooseOneLess.ChooseOneLess
