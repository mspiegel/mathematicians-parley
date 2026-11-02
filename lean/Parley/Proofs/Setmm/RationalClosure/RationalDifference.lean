module

public import Tactics
public import Parley.Proofs.Setmm.RationalClosure.RationalSum

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalDifference

theorem rational_difference (A : ℚ) (B : ℚ) :
    True := by
  -- 1. thm:rational-sum B := −B
  -- 2. substitute
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalDifference
