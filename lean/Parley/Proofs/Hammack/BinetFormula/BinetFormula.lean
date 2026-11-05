module

public import AlgebraTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Parley.Proofs.Hammack.BinetFormula.PowerRecurrence

/-! Written from proofs/hammack/binet-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinetFormula.BinetFormula

set_option maxHeartbeats 400000 in
theorem binet_formula (n : ℕ) (hH1 : 0 < n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (F (n : ℤ) : ℝ) = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n) / Real.sqrt (5 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (5 : ℝ) ≠ 0 := by parley_real
  set φ : ℝ := (1 + Real.sqrt (5 : ℝ)) / 2 with hD2
  have hD2_kind : True := by parley_side
  set ψ : ℝ := (1 - Real.sqrt (5 : ℝ)) / 2 with hD3
  have hD3_kind : True := by parley_side
  -- 2. calculation
  have s2 : φ ^ 2 = φ + 1 := by
    calc φ ^ 2 = ((1 + Real.sqrt (5 : ℝ)) / 2) ^ 2 := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
      _ = (1 + Real.sqrt (5 : ℝ)) / 2 + 1 := by parley_real
      _ = φ + 1 := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  -- 3. calculation
  have s3 : ψ ^ 2 = ψ + 1 := by
    calc ψ ^ 2 = ((1 - Real.sqrt (5 : ℝ)) / 2) ^ 2 := by first | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      _ = (1 - Real.sqrt (5 : ℝ)) / 2 + 1 := by parley_real
      _ = ψ + 1 := by first | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
  -- 4. induction on j starting at 0
  have s4 : ∀ j : ℕ, (F (j : ℤ) : ℝ) = (φ ^ j - ψ ^ j) / Real.sqrt (5 : ℝ) ∧ (G (j : ℤ) : ℝ) = (φ ^ (j + 1) - ψ ^ (j + 1)) / Real.sqrt (5 : ℝ) := by
    intro j
    induction j with
    | zero =>
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
          _ = (φ ^ (0 + 1) - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = (φ ^ (0 + 1) - ψ ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      -- 4.5. join 4.3, 4.4
      have s4_5a : (F 0 : ℝ) = (φ ^ 0 - ψ ^ 0) / Real.sqrt (5 : ℝ) := by parley_side
      have s4_5b : (G 0 : ℝ) = (φ ^ (0 + 1) - ψ ^ (0 + 1)) / Real.sqrt (5 : ℝ) := by parley_side
      all_goals parley_side
    | succ j hIH =>
      -- 4.6. D1
      have s4_6 : F ((j : ℤ) + 1) = G (j : ℤ) := by have h := (hD1.2.2 (((j : ℤ) + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.7. D1
      have s4_7 : G ((j : ℤ) + 1) = F (j : ℤ) + G (j : ℤ) := by have h := (hD1.2.2 (((j : ℤ) + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)
      -- 4.8. substitute G(j) = (φ^(j + 1) − ψ^(j + 1))/√5 (IH) into line 4.6
      have s4_8 : (F ((j : ℤ) + 1) : ℝ) = (φ ^ (j + 1) - ψ ^ (j + 1)) / Real.sqrt (5 : ℝ) := by
        have s4_6_w : (F ((j : ℤ) + 1) : ℝ) = (G (j : ℤ) : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s4_6; push_cast at h; linear_combination (norm := parley_norm) h
        parley_subst_at hIH.2 s4_6_w
      -- 4.9. thm:power-recurrence x := φ, k := j, from 2
      have s4_9 : φ ^ (j + 1 + 1) = φ ^ (j + 1) + φ ^ j := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)) | exact_mod_cast ((Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j))).symm | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := φ) s2 (k := j)); parley_side)
      -- 4.10. thm:power-recurrence x := ψ, k := j, from 3
      have s4_10 : ψ ^ (j + 1 + 1) = ψ ^ (j + 1) + ψ ^ j := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)) | exact_mod_cast ((Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j))).symm | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinetFormula.PowerRecurrence.power_recurrence (x := ψ) s3 (k := j)); parley_side)
      -- 4.11. calculation
      have r101_1 : Real.sqrt (5 : ℝ) ≠ 0 := by parley_side
      have s4_11 : (G ((j : ℤ) + 1) : ℝ) = (φ ^ (j + 1 + 1) - ψ ^ (j + 1 + 1)) / Real.sqrt (5 : ℝ) := by
        calc (G ((j : ℤ) + 1) : ℝ) = (F (j : ℤ) : ℝ) + (G (j : ℤ) : ℝ) := by parley_side
          _ = (φ ^ j - ψ ^ j) / Real.sqrt (5 : ℝ) + (G (j : ℤ) : ℝ) := by parley_subst hIH.1
          _ = (φ ^ j - ψ ^ j) / Real.sqrt (5 : ℝ) + (φ ^ (j + 1) - ψ ^ (j + 1)) / Real.sqrt (5 : ℝ) := by parley_subst hIH.2
          _ = (φ ^ (j + 1 + 1) - ψ ^ (j + 1 + 1)) / Real.sqrt (5 : ℝ) := by linear_combination (norm := parley_field) ((-1) / ((Real.sqrt (5 : ℝ)))) * s4_9 + ((1) / ((Real.sqrt (5 : ℝ)))) * s4_10
      -- 4.12. join 4.8, 4.11
      have s4_12a : (F ((j : ℤ) + 1) : ℝ) = (φ ^ (j + 1) - ψ ^ (j + 1)) / Real.sqrt (5 : ℝ) := by parley_side
      have s4_12b : (G ((j : ℤ) + 1) : ℝ) = (φ ^ (j + 1 + 1) - ψ ^ (j + 1 + 1)) / Real.sqrt (5 : ℝ) := by parley_side
      all_goals parley_side
  -- 5. instantiate j := n in line 4
  have s5 : (F (n : ℤ) : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt (5 : ℝ) ∧ (G (n : ℤ) : ℝ) = (φ ^ (n + 1) - ψ ^ (n + 1)) / Real.sqrt (5 : ℝ) := by first | exact (s4 n) | exact ((s4 n)).symm | simpa using (s4 n) | exact_mod_cast (s4 n) | (have h := (s4 n); parley_side)
  -- 6. calculation
  have s6 : (F (n : ℤ) : ℝ) = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n) / Real.sqrt (5 : ℝ) := by
    calc (F (n : ℤ) : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt (5 : ℝ) := by parley_side
      _ = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n - ψ ^ n) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
      _ = (((1 + Real.sqrt (5 : ℝ)) / 2) ^ n - ((1 - Real.sqrt (5 : ℝ)) / 2) ^ n) / Real.sqrt (5 : ℝ) := by first | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
  all_goals exact s6

end Parley.Proofs.Hammack.BinetFormula.BinetFormula
