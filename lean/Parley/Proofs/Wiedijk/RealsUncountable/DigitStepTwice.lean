module

public import AlgebraTactics
public import ArithTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice

theorem digit_step_twice (t : ℤ) :
    ((t + 1) % (10 : ℤ) + 1) % (10 : ℤ) ≠ t := by
  -- 1. membership, from D2
  -- 2. thm:digit-step-divides
  have s2 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by first | exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t)) | exact ((Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t))).symm | simpa using (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t)) | exact_mod_cast (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t)) | (have h := (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t)); parley_side)
  -- 3. thm:digit-step-divides t := s(t), from 1
  have s3 : (10 : ℤ) ∣ (t + 1) % (10 : ℤ) + 1 - ((t + 1) % (10 : ℤ) + 1) % (10 : ℤ) := by first | exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ))) | exact ((Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ)))).symm | simpa using (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ))) | exact_mod_cast (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ))) | (have h := (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ))); parley_side)
  -- 4. contradiction
  have s4 : ((t + 1) % (10 : ℤ) + 1) % (10 : ℤ) ≠ t := by
    by_contra hc_hS
    have hS : ((t + 1) % (10 : ℤ) + 1) % (10 : ℤ) = t := by parley_suppose hc_hS
    -- 4.1. substitute s(s(t)) = t (S) into line 3
    have s4_1 : (10 : ℤ) ∣ (t + 1) % (10 : ℤ) + 1 - t := by parley_subst_at hS s3
    -- 4.2. mun:divides-sum d := 10, a := (t + 1) − s(t), b := (s(t) + 1) − t, from 2, 4.1
    have s4_2 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) + ((t + 1) % (10 : ℤ) + 1 - t) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1); parley_side)
    -- 4.3. substitute
    have s4_3 : (10 : ℤ) ∣ (2 : ℤ) := by
      have c1 : t + 1 - (t + 1) % (10 : ℤ) + ((t + 1) % (10 : ℤ) + 1 - t) = 2 := by parley_ring
      have row1 : (10 : ℤ) ∣ (2 : ℤ) := by parley_subst_at c1 s4_2
      exact row1
    exact absurd s4_3 (by norm_num)
    all_goals parley_side
  all_goals exact s4

end Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice
