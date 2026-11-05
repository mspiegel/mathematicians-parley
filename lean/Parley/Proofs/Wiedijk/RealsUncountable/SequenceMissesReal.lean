module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber
public import Parley.Proofs.Wiedijk.RealsUncountable.DigitRange
public import Parley.Proofs.Wiedijk.RealsUncountable.DigitStep
public import Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal

set_option maxHeartbeats 600000 in
theorem sequence_misses_real (f : ℤ → ℝ) :
    (∃ x : ℝ, ∀ n : ℕ, 0 < n → f (n : ℤ) ≠ x) := by
  set e : ℤ → ℤ := fun n => (⌊10 ^ n * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) with hD7
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  have s2 : ∀ n : ℕ, 0 < n → (((True ∧ 0 ≤ (e (n : ℤ) : ℝ)) ∧ (e (n : ℤ) : ℝ) ≤ 9) ∧ (e (n : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ)) ∧ (((e (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by
    intro n hK2
    -- 2.1. membership, from D2, 1
    -- 2.2. thm:digit-range t := D(f(n), n), from 1
    have s2_2 : 0 ≤ (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ∧ (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≤ 9 := by first | exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact ((Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ)))).symm | simpa using (Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact_mod_cast (Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | (have h := (Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))); parley_side)
    -- 2.3. thm:digit-step t := D(f(n), n), from 1
    have s2_3 : (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by first | exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact ((Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ)))).symm | simpa using (Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact_mod_cast (Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | (have h := (Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))); parley_side)
    -- 2.4. thm:digit-step-twice t := D(f(n), n), from 1
    have s2_4 : ((((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by first | exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact ((Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ)))).symm | simpa using (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | exact_mod_cast (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))) | (have h := (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ))); parley_side)
    -- 2.5. join 2.1, 2.2, 2.3, 2.4
    have s2_5 : (((True ∧ 0 ≤ (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ)) ∧ (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≤ 9) ∧ (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ)) ∧ ((((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by parley_side
    -- 2.6. D7
    have s2_6 : (e (n : ℤ) : ℝ) = (((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by parley_side
    -- 2.7. substitute e(n) = s(D(f(n), n)) (line 2.6) into line 2.5
    have s2_7 : (((True ∧ 0 ≤ (e (n : ℤ) : ℝ)) ∧ (e (n : ℤ) : ℝ) ≤ 9) ∧ (e (n : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ)) ∧ (((e (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by
      have e_int : e (n : ℤ) = (⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) + 1) % (10 : ℤ) := by exact_mod_cast s2_6
      first | parley_subst_at s2_6 s2_5 | parley_subst_at e_int s2_5
    all_goals exact s2_7
  -- 3. proof
  -- what this block shows, Lean's types give
  -- 4. mun:function-into, from 3
  -- 5. proof
  have s5 : ∀ n : ℕ, 0 < n → 0 ≤ (e (n : ℤ) : ℝ) ∧ (e (n : ℤ) : ℝ) ≤ 9 := by
    intro n hK4
    -- 5.1. inequalities, from 2
    have s5_1 : 0 ≤ (e (n : ℤ) : ℝ) ∧ (e (n : ℤ) : ℝ) ≤ 9 := by have := (s2 n (by parley_side)); parley_side
    all_goals exact s5_1
  -- 6. obtain x: thm:decimal-number d := e, from 5
  obtain ⟨x, s6⟩ := (Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber.decimal_number (d := e) s5)
  -- 7. proof
  have s7 : ∀ n : ℕ, 0 < n → f (n : ℤ) ≠ x := by
    intro n hK5
    by_contra hc_hS
    have hS : f (n : ℤ) = x := by parley_suppose hc_hS
    -- 7.1. instantiate n := n in line 6
    have s7_1 : ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (e (n : ℤ) : ℝ) ∨ ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = (((e (n : ℤ) + 1) % (10 : ℤ) : ℤ) : ℝ) := by first | exact (s6 n (by parley_side)) | exact ((s6 n (by parley_side))).symm | simpa using (s6 n (by parley_side)) | exact_mod_cast (s6 n (by parley_side)) | (have h := (s6 n (by parley_side)); parley_side)
    -- 7.2. cases, from 7.1
    have s7_2 : ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by
      rcases s7_1 with hC1 | hC2
      · skip
        -- 7.2.1. substitute D(x, n) = e(n) (C1) into line 2
        have s7_2_1 : ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by
          have at0 := (s2 n (by parley_side)).1.2
          have e_int : ⌊10 ^ n * x⌋ % (10 : ℤ) = e (n : ℤ) := by exact_mod_cast hC1
          first | parley_subst_at hC1 at0 | parley_subst_at e_int at0
        all_goals parley_side
      · skip
        -- 7.2.2. substitute D(x, n) = s(e(n)) (C2) into line 2
        have s7_2_2 : ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) ≠ ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by
          have at0 := (s2 n (by parley_side)).2
          have e_int : ⌊10 ^ n * x⌋ % (10 : ℤ) = (e (n : ℤ) + 1) % (10 : ℤ) := by exact_mod_cast hC2
          first | parley_subst_at hC2 at0 | parley_subst_at e_int at0
        all_goals parley_side
    -- 7.3. substitute f(n) = x (S)
    have s7_3 : ((⌊10 ^ n * x⌋ % (10 : ℤ) : ℤ) : ℝ) = ((⌊10 ^ n * f (n : ℤ)⌋ % (10 : ℤ) : ℤ) : ℝ) := by parley_subst hS
    all_goals parley_side
  -- 8. exhibit, from 7
  have s8 : ∃ x : ℝ, ∀ n : ℕ, 0 < n → f (n : ℤ) ≠ x := ⟨x, by parley_side⟩
  all_goals exact s8

end Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal
