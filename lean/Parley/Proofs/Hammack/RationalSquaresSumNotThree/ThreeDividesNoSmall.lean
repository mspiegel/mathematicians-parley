module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall

theorem three_divides_no_small (r : ℕ) (hH1 : 0 < r) (hH2 : (r : ℤ) < 3) :
    ¬ (3 : ℤ) ∣ (r : ℤ) := by
  -- the theorem. contradiction
  have sThm : ¬ (3 : ℤ) ∣ (r : ℤ) := by
    by_contra hc_hS
    have hS : (3 : ℤ) ∣ (r : ℤ) := by parley_suppose hc_hS
    -- 1. mun:divides-le e := 3, m := r, from S
    have s1 : 3 ≤ (r : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := 3) (by parley_side) (m := r) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := 3) (by parley_side) (m := r) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := 3) (by parley_side) (m := r) (by parley_side) (by parley_side))
    -- 2. inequalities, from H2
    have s2 : ¬ 3 ≤ (r : ℤ) := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall
