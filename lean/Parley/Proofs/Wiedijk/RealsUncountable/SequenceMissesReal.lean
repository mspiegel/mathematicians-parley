module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
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

theorem sequence_misses_real (f : ℤ → ℝ) :
    (∃ x : ℝ, ∀ n : ℤ, 0 < n → f n ≠ x) := by
  set e : ℤ → ℤ := fun n : ℤ => (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) with hD7
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  have s2 : ∀ n : ℤ, 0 < n → (((True ∧ 0 ≤ e n) ∧ e n ≤ 9) ∧ e n ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)) ∧ (e n + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by
    intro n hK2
    -- 2.1. membership, from D2, 1
    -- 2.2. thm:digit-range t := D(f(n), n), from 1
    have s2_2 : 0 ≤ (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) ∧ (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) ≤ 9 := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitRange.digit_range (t := ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)))
    -- 2.3. thm:digit-step t := D(f(n), n), from 1
    have s2_3 : (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStep.digit_step (t := ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)))
    -- 2.4. thm:digit-step-twice t := D(f(n), n), from 1
    have s2_4 : ((⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepTwice.digit_step_twice (t := ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)))
    -- 2.5. join 2.1, 2.2, 2.3, 2.4
    have s2_5 : (((True ∧ 0 ≤ (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ)) ∧ (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) ≤ 9) ∧ (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)) ∧ ((⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by parley_side
    -- 2.6. D7
    have s2_6 : e n = (⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) + 1) % (10 : ℤ) := by simp (disch := omega) only [hD7]
    -- 2.7. substitute e(n) = s(D(f(n), n)) (line 2.6) into line 2.5
    have s2_7 : (((True ∧ 0 ≤ e n) ∧ e n ≤ 9) ∧ e n ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)) ∧ (e n + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (((True ∧ 0 ≤ t) ∧ t ≤ 9) ∧ t ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ)) ∧ (t + 1) % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ))) s2_6.symm s2_5; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact ⟨⟨⟨⟨trivial, ((((s2_7).1).1).1).2⟩, (((s2_7).1).1).2⟩, ((s2_7).1).2⟩, (s2_7).2⟩
  -- 3. proof
  -- what this block shows, Lean's types give
  -- 4. mun:function-into, from 3
  -- 5. proof
  have s5 : ∀ n : ℤ, 0 < n → 0 ≤ e n ∧ e n ≤ 9 := by
    intro n hK4
    -- 5.1. inequalities, from 2
    have s5_1 : 0 ≤ e n ∧ e n ≤ 9 := by have := (s2 n hK4); parley_side
    exact ⟨(s5_1).1, (s5_1).2⟩
  -- 6. obtain x: thm:decimal-number d := e, from 5
  obtain ⟨x, s6⟩ := (Parley.Proofs.Wiedijk.RealsUncountable.DecimalNumber.decimal_number (d := e) s5)
  -- 7. proof
  have s7 : ∀ n : ℤ, 0 < n → f n ≠ x := by
    intro n hK5
    intro hS
    -- 7.1. instantiate n := n in line 6
    have s7_1 : ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = e n ∨ ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = (e n + 1) % (10 : ℤ) := by exact (s6 n hK5)
    -- 7.2. cases, from 7.1
    have s7_2 : ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by
      rcases s7_1 with hC1 | hC2
      · skip
        -- 7.2.1. substitute D(x, n) = e(n) (C1) into line 2
        (have h := Eq.subst (motive := (fun t : ℤ => t ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ))) hC1.symm (s2 n hK5).1.2; push_cast at h ⊢; all_goals exact_mod_cast h)
      · skip
        -- 7.2.2. substitute D(x, n) = s(e(n)) (C2) into line 2
        (have h := Eq.subst (motive := (fun t : ℤ => t ≠ ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ))) hC2.symm (s2 n hK5).2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 7.3. substitute f(n) = x (S)
    have s7_3 : ⌊10 ^ n.toNat * x⌋ % (10 : ℤ) = ⌊10 ^ n.toNat * f n⌋ % (10 : ℤ) := by (have h := congrArg (fun t : ℝ => ((⌊10 ^ n.toNat * t⌋ % (10 : ℤ) : ℤ) : ℝ)) hS.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact s7_2 s7_3
  -- 8. exhibit, from 7
  exact ⟨x, s7⟩

end Parley.Proofs.Wiedijk.RealsUncountable.SequenceMissesReal
