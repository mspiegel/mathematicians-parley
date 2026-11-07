module

public import AlgebraTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.LimitLemmas.ScaledSmall

/-! Written from proofs/setmm/a-over-n-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AOverNLimit.AOverNTendsToZero

set_option maxHeartbeats 400000 in
theorem a_over_n_tends_to_zero (A : ℝ) :
    Filter.Tendsto (fun n : ℤ => (A / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. mun:abs-nonneg x := A
  have s1 : abs A ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (A : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (A : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (A : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (A : ℂ))); parley_side)
  -- 2. inequalities, from 1
  have s2 : abs A + 1 > 0 := by parley_order
  -- 3. inequalities
  have s3 : 2 * (abs A + 1) > 0 := by parley_order
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. proof
  have s5 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (A / (n : ℝ)) < ε)) := by
    intro ε
    intro hA1
    -- 5.1. membership
    have r42_1 : 2 * (abs A + 1) ≠ 0 := by parley_side
    -- 5.2. mun:quotient-positive x := ε, y := 2·(|A| + 1), from A1, 3
    have s5_2 : ε / (2 * (abs A + 1)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs A + 1)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs A + 1)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs A + 1)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs A + 1)) (by parley_side) (by parley_side)); parley_side)
    -- 5.3. obtain N: thm:archimedean x := ε/(2·(|A| + 1)), from 5.1, 5.2
    obtain ⟨N, s5_3a, s5_3b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / (2 * (abs A + 1))) (by parley_side))
    -- 5.4. proof
    have s5_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (A / (n : ℝ)) < ε := by
      intro n hK3
      intro hA2
      -- 5.4.1. mun:reciprocal-order x := N, y := n, from A2
      have r57_1 : N > 0 := by parley_order
      have r57_2 : n > 0 := by parley_order
      have s5_4_1 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 5.4.2. transitivity, from 5.4.1, 5.3
      have r62_1 : 2 * (abs A + 1) ≠ 0 := by parley_side
      have s5_4_2 : 1 / (n : ℝ) < ε / (2 * (abs A + 1)) := by parley_order
      -- 5.4.3. mun:reciprocal-positive x := n
      have r66_1 : n > 0 := by parley_order
      have s5_4_3 : 1 / (n : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by parley_side)); parley_side)
      -- 5.4.4. inequalities
      have s5_4_4 : 1 / (n : ℚ) ≥ 0 := by parley_order
      -- 5.4.5. substitute
      have s5_4_5 : abs (1 / (n : ℝ)) < ε / (2 * (abs A + 1)) := by
        have c1 : 1 / (n : ℚ) = abs (1 / (n : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (n : ℚ))) (by parley_side); parley_side)
        have c1_w : 1 / (n : ℝ) = abs (1 / (n : ℝ)) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
        have row1 : abs (1 / (n : ℝ)) < ε / (2 * (abs A + 1)) := by first | parley_put_at c1_w s5_4_2 | parley_put_at c1 s5_4_2 | parley_subst_at c1_w s5_4_2 | parley_subst_at c1 s5_4_2
        exact row1
      -- 5.4.6. thm:scaled-small C := A, u := 1/n, from A1, 5.4.5
      have s5_4_6 : abs (A * (1 / (n : ℝ))) < ε := by first | linarith [(Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := A) (u := 1 / (n : ℝ)) (ε := ε) hA1 (by parley_side))] | (have h := (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := A) (u := 1 / (n : ℝ)) (ε := ε) hA1 (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := A) (u := 1 / (n : ℝ)) (ε := ε) hA1 (by parley_side)) | (have h := (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := A) (u := 1 / (n : ℝ)) (ε := ε) hA1 (by parley_side)); parley_side)
      -- 5.4.7. substitute
      have s5_4_7 : abs (A / (n : ℝ)) < ε := by
        have c1 : A * (1 / (n : ℝ)) = A / (n : ℝ) := by parley_ring
        have row1 : abs (A / (n : ℝ)) < ε := by parley_subst_at c1 s5_4_6
        exact row1
      all_goals parley_side
    -- 5.5. exhibit, from 5.4
    have s5_5 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (A / (n : ℝ)) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 6. def:tends-to L := 0, from 4, 5
  have s6 : Filter.Tendsto (fun n : ℤ => (A / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => A / (n : ℝ))) (L := (0 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => A / (n : ℝ))) (L := (0 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s6

end Parley.Proofs.Setmm.AOverNLimit.AOverNTendsToZero
