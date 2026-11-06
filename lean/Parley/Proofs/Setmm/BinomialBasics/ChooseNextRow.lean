module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow

theorem choose_next_row (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ N := by parley_order
  have s1b : N ≤ N + 1 := by parley_order
  -- 2. def:range-between k := N, a := 0, b := N + 1, from 1
  have s2 : N ∈ Finset.Icc (0 : ℤ) (N + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N + 1))).mpr (by parley_side); parley_side)
  -- 3. algebra
  have s3 : N + 1 - N = 1 := by parley_ring
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = 1 := by
    calc (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_subst s3
      _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
  -- 5. def:factorial n := N
  have s5 : (LeanBridges.Counting.factorial (N + 1) : ℤ) = (LeanBridges.Counting.factorial N : ℤ) * (N + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) (by parley_side)); parley_side)
  -- 6. calculation
  have s6 : (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
    try qify
    calc (LeanBridges.Counting.choose (N + 1) N : ℚ) = (LeanBridges.Counting.factorial (N + 1) : ℚ) / ((LeanBridges.Counting.factorial (N + 1 - N) : ℚ) * (LeanBridges.Counting.factorial N : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (by parley_side) (k := N)) (by parley_side); parley_side)
      _ = (LeanBridges.Counting.factorial (N + 1) : ℚ) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
          have s4_w : (LeanBridges.Counting.factorial (N + 1 - N) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s4_w | parley_subst s4
      _ = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
          have s5_w : (LeanBridges.Counting.factorial (N + 1) : ℚ) = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s5; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s5_w | parley_subst s5
      _ = (N : ℚ) + 1 := by parley_ring
  all_goals exact s6

end Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow
