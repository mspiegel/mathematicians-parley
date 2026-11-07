module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/preimage-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn

theorem square_window_in (t : ℝ) (hH2 : 3 ≤ t) (hH3 : t ≤ 4) :
    12 ≤ t ^ 2 + 3 ∧ t ^ 2 + 3 ≤ 19 := by
  -- 1. inequalities, from H2
  have s1 : t ≥ 0 := by parley_order
  -- 2. mun:square-le x := 3, y := t, from H2, 1
  have r22_1 : (3 : ℤ) ≥ 0 := by parley_arith
  have s2 : 3 ^ 2 ≤ t ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  -- 3. mun:square-le x := t, y := 4, from H3, 1
  have r26_1 : (4 : ℤ) ≥ 0 := by parley_arith
  have s3 : t ^ 2 ≤ 4 ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  -- 4. inequalities
  have s4 : 12 ≤ t ^ 2 + 3 := by parley_order
  -- 5. inequalities
  have s5 : t ^ 2 + 3 ≤ 19 := by parley_order
  -- 6. join 4, 5
  have s6a : 12 ≤ t ^ 2 + 3 := by parley_side
  have s6b : t ^ 2 + 3 ≤ 19 := by parley_side
  exact ⟨by parley_side, by parley_side⟩

end Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowIn
