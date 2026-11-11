module

public import AlgebraTactics
public import SubstTactics
public import Tactics
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
  have s2 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t))
  -- 3. thm:digit-step-divides t := s(t), from 1
  have s3 : (10 : ℤ) ∣ (t + 1) % (10 : ℤ) + 1 - ((t + 1) % (10 : ℤ) + 1) % (10 : ℤ) := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := (t + 1) % (10 : ℤ)))
  -- 4. contradiction
  intro hS
  -- 4.1. substitute s(s(t)) = t (S) into line 3
  have s4_1 : (10 : ℤ) ∣ (t + 1) % (10 : ℤ) + 1 - t := by parley_subst_at hS s3
  -- 4.2. mun:divides-sum d := 10, a := (t + 1) − s(t), b := (s(t) + 1) − t, from 2, 4.1
  have s4_2 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) + ((t + 1) % (10 : ℤ) + 1 - t) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (10 : ℤ)) (a := t + 1 - (t + 1) % (10 : ℤ)) (b := (t + 1) % (10 : ℤ) + 1 - t) s2 s4_1)
  -- 4.3. substitute
  have s4_3 : (10 : ℤ) ∣ (2 : ℤ) := by
    have c1 : t + 1 - (t + 1) % (10 : ℤ) + ((t + 1) % (10 : ℤ) + 1 - t) = 2 := by parley_ring
    have row1 : (10 : ℤ) ∣ (2 : ℤ) := by (have h := Eq.subst (motive := (fun u : ℤ => (10 : ℤ) ∣ u)) c1 s4_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  exact absurd s4_3 (by norm_num)

end Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice
