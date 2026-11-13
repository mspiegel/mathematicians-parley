module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/preimage-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut

theorem square_window_out (t : ℝ) (hH2 : t ≥ 0) (hH3 : 12 ≤ t ^ 2 + 3) (hH4 : t ^ 2 + 3 ≤ 19) :
    3 ≤ t ∧ t ≤ 4 := by
  -- 1. inequalities
  have s1 : 3 ^ 2 ≤ t ^ 2 := by linarith only [hH3]
  -- 2. inequalities
  have s2 : t ^ 2 ≤ 4 ^ 2 := by linarith only [hH4]
  -- 3. mun:square-le x := 3, y := t, from H2, 1
  have r66_1 : (3 : ℤ) ≥ 0 := by parley_arith
  have s3 : 3 ≤ t := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by norm_num) hH2)).mpr s1
  -- 4. mun:square-le x := t, y := 4, from H2, 2
  have r70_1 : (4 : ℤ) ≥ 0 := by parley_arith
  have s4 : t ≤ 4 := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) hH2 (by norm_num))).mpr s2
  -- 5. join 3, 4
  have s5a : 3 ≤ t := s3
  have s5b : t ≤ 4 := s4
  exact ⟨s5a, s5b⟩

end Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut
