module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorOfInteger

theorem floor_of_integer (A : ℤ) :
    ⌊(A : ℚ)⌋ = A := by
  -- 1. inequalities
  have s1 : A ≤ A := by parley_side
  -- 2. inequalities
  have s2 : A < A + 1 := by parley_side
  -- 3. mun:floor-between x := A, k := A, from 1, 2
  have s3 : ⌊(A : ℚ)⌋ = A := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A) (k := A))).mpr (by parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.FloorBasics.FloorOfInteger
