module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/distance-triangle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle

theorem distance_triangle (A : ℝ) (B : ℝ) (C : ℝ) :
    abs (A - B) ≤ abs (A - C) + abs (C - B) := by
  -- 1. thm:triangle-inequality a := A − C, b := C − B
  have s1 : abs (A - C + (C - B)) ≤ abs (A - C) + abs (C - B) := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - C) (b := C - B))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - C) (b := C - B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - C) (b := C - B))
  -- 2. substitute
  have s2 : abs (A - B) ≤ abs (A - C) + abs (C - B) := by
    have c1 : A - C + (C - B) = A - B := by parley_ring
    have row1 : abs (A - B) ≤ abs (A - C) + abs (C - B) := by parley_subst_at c1 s1
    exact row1
  all_goals parley_side

end Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle
