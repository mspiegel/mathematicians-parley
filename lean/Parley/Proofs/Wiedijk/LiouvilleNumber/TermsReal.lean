module

public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

theorem terms_real (m : ℤ) (hH1 : 0 < m) :
    True := by
  -- the theorem. proof
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal
