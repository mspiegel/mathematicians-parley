module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/reverse-triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow

theorem abs_difference_below (A : ℝ) (B : ℝ) :
    |A| - |B| ≤ |A - B| := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : |A - B + B| ≤ |A - B| + |B| := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))
  -- 2. substitute
  have s2 : |A| ≤ |A - B| + |B| := by
    have c1 : A - B + B = A := by parley_ring
    have row1 : |A| ≤ |A - B| + |B| := by parley_subst_at c1 s1
    exact row1
  -- 3. inequalities
  have s3 : |A| - |B| ≤ |A - B| := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow
