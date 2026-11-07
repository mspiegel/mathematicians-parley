module

public import ArithTactics
public import OrderTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/ln-above-one-is-positive.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LnAboveOneIsPositive.LnAboveOneIsPositive

theorem ln_above_one_is_positive (x : ℝ) (hH2 : x > 1) :
    Real.log x > 0 := by
  -- 1. inequalities, from H2
  have s1 : x > 0 := by parley_order
  -- 2. mun:ln-order x := 1, y := x, from H2, 1
  have r13_1 : (1 : ℤ) > 0 := by parley_arith
  have s2 : Real.log (1 : ℝ) < Real.log x := by first | linarith [((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := (1 : ℝ)) (y := x) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  -- 3. real arithmetic
  have s3 : Real.log (1 : ℝ) = 0 := by parley_real
  -- 4. substitute ln(1) = 0 (line 3) into line 2
  have s4 : Real.log x > 0 := by parley_subst_at s3 s2
  all_goals exact s4

end Parley.Proofs.Identities.LnAboveOneIsPositive.LnAboveOneIsPositive
