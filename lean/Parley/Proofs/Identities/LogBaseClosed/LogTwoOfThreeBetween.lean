module

public import AlgebraTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/log-base-closed.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseClosed.LogTwoOfThreeBetween

theorem log_two_of_three_between :
    (1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) ∧ Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2) := by
  -- 1. mun:quotient-positive x := ln(3) − ln(2), y := ln(2)
  have r37_1 : Real.log (3 : ℝ) - Real.log (2 : ℝ) > 0 := by parley_real
  have r37_2 : Real.log (2 : ℝ) > 0 := by parley_real
  have s1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) r37_1 r37_2)
  -- 2. substitute
  have r42_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s2 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := by
    have c1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 := by parley_ring
    have row1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 3. inequalities, from 2
  have r48_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s3 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) := by linarith only [s2]
  -- 4. mun:quotient-positive x := 2·ln(2) − ln(3), y := ln(2)
  have r52_1 : 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) > 0 := by parley_real
  have r52_2 : Real.log (2 : ℝ) > 0 := by parley_real
  have s4 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) r52_1 r52_2)
  -- 5. substitute
  have r57_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s5 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by
    have c1 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) = 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) := by parley_ring
    have row1 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t > 0)) c1 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 6. inequalities
  have r63_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s6 : Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := by linarith only [s5]
  -- 7. join 3, 6
  have s7 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) ∧ Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := ⟨s3, s6⟩
  exact ⟨(s7).1, (s7).2⟩

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfThreeBetween
