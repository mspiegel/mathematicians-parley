module

public import AlgebraTactics
public import ComplexTactics
public import Functions
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/wiedijk/de-moivre.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DeMoivre.DeMoivre

set_option maxHeartbeats 400000 in
theorem de_moivre (x : ℝ) (n : ℤ) (hH2 : 0 ≤ n) :
    ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ n.toNat = (Real.cos ((n : ℝ) * x) : ℂ) + Complex.I * (Real.sin ((n : ℝ) * x) : ℂ) := by
  -- 1. def:i
  have s1 : Complex.I * Complex.I = -1 := by exact Parley.Items.Stdlib.Numbers.def_i
  -- 2. induction on k starting at 0
  have s2 : ∀ k : ℤ, 0 ≤ k → ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ k.toNat = (Real.cos ((k : ℝ) * x) : ℂ) + Complex.I * (Real.sin ((k : ℝ) * x) : ℂ) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. algebra
      have s2_1 : 0 * x = 0 := by parley_ring
      -- 2.2. substitute cos(0) = 1 (real arithmetic)
      have s2_2 : (Real.cos (0 : ℝ) : ℂ) + Complex.I * (Real.sin (0 : ℝ) : ℂ) = 1 + Complex.I * (Real.sin (0 : ℝ) : ℂ) := by parley_subst (show (Real.cos (0 : ℝ) : ℂ) = 1 by parley_real)
      -- 2.3. substitute sin(0) = 0 (real arithmetic)
      have s2_3 : 1 + Complex.I * (Real.sin (0 : ℝ) : ℂ) = 1 + Complex.I * 0 := by parley_subst (show (Real.sin (0 : ℝ) : ℂ) = 0 by parley_real)
      -- 2.4. calculation
      have s2_4 : ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ 0 = (Real.cos (0 * x) : ℂ) + Complex.I * (Real.sin (0 * x) : ℂ) := by
        calc ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ 0 = 1 := by parley_ring
          _ = 1 + Complex.I * 0 := by parley_ring
          _ = 1 + Complex.I * (Real.sin (0 : ℝ) : ℂ) := by parley_side
          _ = (Real.cos (0 : ℝ) : ℂ) + Complex.I * (Real.sin (0 : ℝ) : ℂ) := by parley_side
          _ = (Real.cos (0 * x) : ℂ) + Complex.I * (Real.sin (0 * x) : ℂ) := by
              have s2_1_w : 0 * (x : ℂ) = 0 := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_1; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_1_w | parley_subst s2_1
      all_goals parley_side
    | succ k hK hIH =>
      -- 2.5. thm:cos-add a := k·x, b := x
      have s2_5 : Real.cos ((k : ℝ) * x + x) = Real.cos ((k : ℝ) * x) * Real.cos x - Real.sin ((k : ℝ) * x) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_side)
      -- 2.6. thm:sin-add a := k·x, b := x
      have s2_6 : Real.sin ((k : ℝ) * x + x) = Real.sin ((k : ℝ) * x) * Real.cos x + Real.cos ((k : ℝ) * x) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))); parley_side)
      -- 2.7. algebra
      have s2_7 : (k : ℝ) * x + x = ((k : ℝ) + 1) * x := by parley_ring
      -- 2.8. calculation
      have s2_8 : ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ (k + 1).toNat = (Real.cos (((k : ℝ) + 1) * x) : ℂ) + Complex.I * (Real.sin (((k : ℝ) + 1) * x) : ℂ) := by
        calc ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ (k + 1).toNat = ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ k.toNat * ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) (m := k) (by parley_side))
          _ = ((Real.cos ((k : ℝ) * x) : ℂ) + Complex.I * (Real.sin ((k : ℝ) * x) : ℂ)) * ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) := by parley_subst hIH
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) + Complex.I * Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by parley_ring
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) + -1 * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by parley_subst s1
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) - (Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by parley_ring
          _ = (Real.cos ((k : ℝ) * x + x) : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by
              have s2_5_w : (Real.cos ((k : ℝ) * x + x) : ℂ) = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) - (Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_5_w | parley_subst s2_5
          _ = (Real.cos ((k : ℝ) * x + x) : ℂ) + Complex.I * (Real.sin ((k : ℝ) * x + x) : ℂ) := by
              have s2_6_w : (Real.sin ((k : ℝ) * x + x) : ℂ) = (Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_6; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_6_w | parley_subst s2_6
          _ = (Real.cos (((k : ℝ) + 1) * x) : ℂ) + Complex.I * (Real.sin (((k : ℝ) + 1) * x) : ℂ) := by
              have s2_7_w : (k : ℂ) * (x : ℂ) + (x : ℂ) = ((k : ℂ) + 1) * (x : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2_7; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_7_w | parley_subst s2_7
      all_goals parley_side
  -- 3. instantiate k := n in line 2
  have s3 : ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ n.toNat = (Real.cos ((n : ℝ) * x) : ℂ) + Complex.I * (Real.sin ((n : ℝ) * x) : ℂ) := by first | linear_combination (norm := parley_norm) (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s2 n (by parley_side)) | exact_mod_cast ((s2 n (by parley_side))).symm | (have h := (s2 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); parley_int_power h) | (have h := (s2 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s2 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); parley_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.DeMoivre.DeMoivre
