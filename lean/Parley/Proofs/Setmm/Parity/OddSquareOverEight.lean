module

public import Parley.Library

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.OddSquareOverEight

theorem odd_square_over_eight (N : ℤ) :
    ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
  set M : ℤ := 2 * N + 1 with D1
  -- 1. calculation
  have s1 : ((M : ℚ) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
    calc ((M : ℚ) ^ 2 - 1) / 8 = ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 := by
          have D1_w : (M : ℚ) = 2 * (N : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) D1; push_cast at h; linear_combination h
          parley_subst D1_w
      _ = (N : ℚ) * ((N : ℚ) + 1) / 2 := by parley_ring
  all_goals parley_side

end Parley.Proofs.Setmm.Parity.OddSquareOverEight
