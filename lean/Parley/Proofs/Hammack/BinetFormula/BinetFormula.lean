module

public import AlgebraTactics
public import Functions
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Parley.Proofs.Hammack.BinetFormula.PowerRecurrence

/-! Written from proofs/hammack/binet-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinetFormula.BinetFormula

set_option maxHeartbeats 400000 in
theorem binet_formula (n : ℤ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (F n : ℝ) = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n.toNat - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n.toNat) / Real.sqrt (5 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (5 : ℝ) ≠ 0 := by parley_real
  set φ : ℝ := (1 + Real.sqrt (5 : ℝ)) / 2 with hD2
  have hD2_kind : True := by parley_side
  set ψ : ℝ := (1 - Real.sqrt (5 : ℝ)) / 2 with hD3
  have hD3_kind : True := by parley_side
  -- 2. calculation
  have s2 : φ ^ 2 = φ + 1 := by
    calc φ ^ 2 = ((1 + Real.sqrt (5 : ℝ)) / 2) ^ 2 := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
      _ = (1 + Real.sqrt (5 : ℝ)) / 2 + 1 := by parley_real
      _ = φ + 1 := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  -- 3. calculation
  have s3 : ψ ^ 2 = ψ + 1 := by
    calc ψ ^ 2 = ((1 - Real.sqrt (5 : ℝ)) / 2) ^ 2 := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      _ = (1 - Real.sqrt (5 : ℝ)) / 2 + 1 := by parley_real
      _ = ψ + 1 := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
  -- 4. induction on j starting at 0
  have s4 : ∀ j : ℤ, 0 ≤ j → (F j : ℝ) = (φ ^ j.toNat - ψ ^ j.toNat) / Real.sqrt (5 : ℝ) ∧ (G j : ℝ) = (φ ^ (j + 1).toNat - ψ ^ (j + 1).toNat) / Real.sqrt (5 : ℝ) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 4.1. D1
      have s4_1 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.2. D1
      have s4_2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.3. calculation
      have s4_3 : (F 0 : ℝ) = (φ ^ 0 - ψ ^ 0) / Real.sqrt (5 : ℝ) := by
        calc (F 0 : ℝ) = 0 := by parley_side
          _ = (φ ^ 0 - ψ ^ 0) / Real.sqrt (5 : ℝ) := by parley_ring
      -- 4.4. calculation
      have s4_4 : (G 0 : ℝ) = (φ ^ (0 + 1) - ψ ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by
        calc (G 0 : ℝ) = 1 := by parley_side
          _ = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ (0 + 1) - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by parley_real
          _ = (φ ^ (0 + 1) - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = (φ ^ (0 + 1) - ψ ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      -- 4.5. join 4.3, 4.4
      have s4_5a : (F 0 : ℝ) = (φ ^ 0 - ψ ^ 0) / Real.sqrt (5 : ℝ) := by parley_side
      have s4_5b : (G 0 : ℝ) = (φ ^ (0 + 1) - ψ ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by parley_side
      all_goals parley_side
    | succ j hK hIH =>
      -- 4.6. D1
      have s4_6 : F (j + 1) = G j := by have h := (hD1.2.2 ((j + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.7. D1
      have s4_7 : G (j + 1) = F j + G j := by have h := (hD1.2.2 ((j + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.8. substitute G(j) = (φ^(j + 1) − ψ^(j + 1))/√5 (IH) into line 4.6
      have s4_8 : (F (j + 1) : ℝ) = (φ ^ (j + 1).toNat - ψ ^ (j + 1).toNat) / Real.sqrt (5 : ℝ) := by
        have s4_6_w : (F (j + 1) : ℝ) = (G j : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s4_6; push_cast at h; linear_combination (norm := parley_norm) h
        parley_subst_at hIH.2 s4_6_w
      -- 4.9. thm:power-recurrence x := φ, k := j, from 2
      have s4_9 : φ ^ (j + 1 + 1).toNat = φ ^ (j + 1).toNat + φ ^ j.toNat := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j) (by parley_side)); parley_side)
      -- 4.10. thm:power-recurrence x := ψ, k := j, from 3
      have s4_10 : ψ ^ (j + 1 + 1).toNat = ψ ^ (j + 1).toNat + ψ ^ j.toNat := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j) (by parley_side)); parley_side)
      -- 4.11. calculation
      have r101_1 : Real.sqrt (5 : ℝ) ≠ 0 := by parley_side
      have s4_11 : (G (j + 1) : ℝ) = (φ ^ (j + 1 + 1).toNat - ψ ^ (j + 1 + 1).toNat) / Real.sqrt (5 : ℝ) := by
        calc (G (j + 1) : ℝ) = (F j : ℝ) + (G j : ℝ) := by parley_side
          _ = (φ ^ j.toNat - ψ ^ j.toNat) / Real.sqrt (5 : ℝ) + (G j : ℝ) := by parley_subst hIH.1
          _ = (φ ^ j.toNat - ψ ^ j.toNat) / Real.sqrt (5 : ℝ) + (φ ^ (j + 1).toNat - ψ ^ (j + 1).toNat) / Real.sqrt (5 : ℝ) := by parley_subst hIH.2
          _ = (φ ^ (j + 1 + 1).toNat - ψ ^ (j + 1 + 1).toNat) / Real.sqrt (5 : ℝ) := by linear_combination (norm := parley_field) ((-1) / ((Real.sqrt (5 : ℝ)))) * s4_9 + ((1) / ((Real.sqrt (5 : ℝ)))) * s4_10
      -- 4.12. join 4.8, 4.11
      have s4_12a : (F (j + 1) : ℝ) = (φ ^ (j + 1).toNat - ψ ^ (j + 1).toNat) / Real.sqrt (5 : ℝ) := by parley_side
      have s4_12b : (G (j + 1) : ℝ) = (φ ^ (j + 1 + 1).toNat - ψ ^ (j + 1 + 1).toNat) / Real.sqrt (5 : ℝ) := by parley_side
      all_goals parley_side
  -- 5. instantiate j := n in line 4
  have s5 : (F n : ℝ) = (φ ^ n.toNat - ψ ^ n.toNat) / Real.sqrt (5 : ℝ) ∧ (G n : ℝ) = (φ ^ (n + 1).toNat - ψ ^ (n + 1).toNat) / Real.sqrt (5 : ℝ) := by first | exact (s4 n (by parley_side)) | exact ((s4 n (by parley_side))).symm | simpa using (s4 n (by parley_side)) | exact_mod_cast (s4 n (by parley_side)) | (have h := (s4 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s4 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s4 n (by parley_side)); parley_side)
  -- 6. calculation
  have s6 : (F n : ℝ) = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n.toNat - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n.toNat) / Real.sqrt (5 : ℝ) := by
    calc (F n : ℝ) = (φ ^ n.toNat - ψ ^ n.toNat) / Real.sqrt (5 : ℝ) := by first | parley_side | parley_line_toNat s5
      _ = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n.toNat - ψ ^ n.toNat) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD2
      _ = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n.toNat - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n.toNat) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD3
  all_goals exact s6

end Parley.Proofs.Hammack.BinetFormula.BinetFormula
