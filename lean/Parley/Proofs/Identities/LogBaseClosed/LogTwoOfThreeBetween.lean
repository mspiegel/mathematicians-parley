module

public import AlgebraTactics
public import OrderTactics
public import RealTactics
public import SubstTactics
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
  have s1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ) - Real.log (2 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 2. substitute
  have r42_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s2 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := by
    have c1 : (Real.log (3 : ℝ) - Real.log (2 : ℝ)) / Real.log (2 : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 := by parley_ring
    have row1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) - 1 > 0 := by parley_subst_at c1 s1
    exact row1
  -- 3. inequalities, from 2
  have r48_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s3 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) := by parley_order
  -- 4. mun:quotient-positive x := 2·ln(2) − ln(3), y := ln(2)
  have r52_1 : 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) > 0 := by parley_real
  have r52_2 : Real.log (2 : ℝ) > 0 := by parley_real
  have s4 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 5. substitute
  have r57_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s5 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by
    have c1 : (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) / Real.log (2 : ℝ) = 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) := by parley_ring
    have row1 : 2 - Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by parley_subst_at c1 s4
    exact row1
  -- 6. inequalities
  have r63_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s6 : Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := by parley_order
  -- 7. join 3, 6
  have s7 : 1 < Real.log (3 : ℝ) / Real.log (2 : ℝ) ∧ Real.log (3 : ℝ) / Real.log (2 : ℝ) < 2 := by parley_side
  all_goals exact s7

end Parley.Proofs.Identities.LogBaseClosed.LogTwoOfThreeBetween
