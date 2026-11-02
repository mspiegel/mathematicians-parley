module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/preimage-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut

theorem square_window_out (t : ℝ) (hH2 : t ≥ 0) (hH3 : 12 ≤ t ^ 2 + 3) (hH4 : t ^ 2 + 3 ≤ 19) :
    3 ≤ t ∧ t ≤ 4 := by
  -- 1. inequalities
  have s1 : 3 ^ 2 ≤ t ^ 2 := by parley_order
  -- 2. inequalities
  have s2 : t ^ 2 ≤ 4 ^ 2 := by parley_order
  -- 3. mun:square-le x := 3, y := t, from H2, 1
  have r66_1 : (3 : ℤ) ≥ 0 := by parley_arith
  have s3 : 3 ≤ t := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (3 : ℝ)) (y := t) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 4. mun:square-le x := t, y := 4, from H2, 2
  have r70_1 : (4 : ℤ) ≥ 0 := by parley_arith
  have s4 : t ≤ 4 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := t) (y := (4 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 5. join 3, 4
  have s5a : 3 ≤ t := by parley_side
  have s5b : t ≤ 4 := by parley_side
  exact ⟨by parley_side, by parley_side⟩

end Parley.Proofs.Hammack.PreimageOfParabola.SquareWindowOut
