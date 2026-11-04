module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/negative-quadratic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NegativeQuadratic.NegativeQuadratic

theorem negative_quadratic (x : ℝ) (hH2 : x ^ 2 + 5 * x < 0) :
    x < 0 := by
  -- the theorem. contradiction
  have sThm : x < 0 := by
    by_contra hc_hS
    have hS : ¬ x < 0 := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : x ≥ 0 := by parley_order
    -- 2. mun:square-nonneg
    have s2 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_side)
    -- 3. inequalities
    have s3 : 5 * x ≥ 0 := by parley_order
    -- 4. inequalities, from 2, 3
    have s4 : x ^ 2 + 5 * x ≥ 0 := by parley_order
    -- 5. inequalities, from 4
    have s5 : ¬ x ^ 2 + 5 * x < 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.NegativeQuadratic.NegativeQuadratic
