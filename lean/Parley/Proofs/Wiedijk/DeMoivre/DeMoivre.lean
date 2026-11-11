module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
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
          _ = 1 + Complex.I * (Real.sin (0 : ℝ) : ℂ) := by exact s2_3.symm
          _ = (Real.cos (0 : ℝ) : ℂ) + Complex.I * (Real.sin (0 : ℝ) : ℂ) := by exact s2_2.symm
          _ = (Real.cos (0 * x) : ℂ) + Complex.I * (Real.sin (0 * x) : ℂ) := by (have h := congrArg (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) (s2_1).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s2_4
    | succ k hK hIH =>
      -- 2.5. thm:cos-add a := k·x, b := x
      have s2_5 : Real.cos ((k : ℝ) * x + x) = Real.cos ((k : ℝ) * x) * Real.cos x - Real.sin ((k : ℝ) * x) * Real.sin x := by
        have hI : Real.cos ((k : ℝ) * x + x) = Real.cos ((k : ℝ) * x) * Real.cos x - Real.sin ((k : ℝ) * x) * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))))
        exact hI
      -- 2.6. thm:sin-add a := k·x, b := x
      have s2_6 : Real.sin ((k : ℝ) * x + x) = Real.sin ((k : ℝ) * x) * Real.cos x + Real.cos ((k : ℝ) * x) * Real.sin x := by
        have hI : Real.sin ((k : ℝ) * x + x) = Real.sin ((k : ℝ) * x) * Real.cos x + Real.cos ((k : ℝ) * x) * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (k : ℂ) * (x : ℂ)) (b := (x : ℂ))))
        exact hI
      -- 2.7. algebra
      have s2_7 : (k : ℝ) * x + x = ((k : ℝ) + 1) * x := by parley_ring
      -- 2.8. calculation
      have s2_8 : ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ (k + 1).toNat = (Real.cos (((k : ℝ) + 1) * x) : ℂ) + Complex.I * (Real.sin (((k : ℝ) + 1) * x) : ℂ) := by
        calc ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ (k + 1).toNat = ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) ^ k.toNat * ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) (m := k) (by parley_side))
          _ = ((Real.cos ((k : ℝ) * x) : ℂ) + Complex.I * (Real.sin ((k : ℝ) * x) : ℂ)) * ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) := by (have h := congrArg (fun t : ℂ => t * ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ))) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) + Complex.I * Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by parley_ring
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) + -1 * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by (have h := congrArg (fun t : ℂ => (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) + t * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ))) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) - (Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by parley_ring
          _ = (Real.cos ((k : ℝ) * x + x) : ℂ) + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ)) := by
              have e_w : (Real.cos ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) - (Real.sin ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) = (Real.cos ((k : ℝ) * x + x) : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) (s2_5).symm; push_cast at h; linear_combination (norm := parley_norm) h
              (have h := congrArg (fun t : ℂ => t + Complex.I * ((Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (Real.cos ((k : ℝ) * x + x) : ℂ) + Complex.I * (Real.sin ((k : ℝ) * x + x) : ℂ) := by
              have e_w : (Real.sin ((k : ℝ) * x) : ℂ) * (Real.cos x : ℂ) + (Real.cos ((k : ℝ) * x) : ℂ) * (Real.sin x : ℂ) = (Real.sin ((k : ℝ) * x + x) : ℂ) := by have h := congrArg (fun x : ℝ => (x : ℂ)) (s2_6).symm; push_cast at h; linear_combination (norm := parley_norm) h
              (have h := congrArg (fun t : ℂ => (Real.cos ((k : ℝ) * x + x) : ℂ) + Complex.I * t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (Real.cos (((k : ℝ) + 1) * x) : ℂ) + Complex.I * (Real.sin (((k : ℝ) + 1) * x) : ℂ) := by (have h := congrArg (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) s2_7; push_cast at h ⊢; all_goals exact_mod_cast h)
      (have h := s2_8; push_cast at h ⊢; all_goals exact h)
  -- 3. instantiate k := n in line 2
  exact (s2 n (by parley_side))

end Parley.Proofs.Wiedijk.DeMoivre.DeMoivre
