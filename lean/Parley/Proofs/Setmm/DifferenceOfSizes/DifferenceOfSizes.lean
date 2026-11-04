module

public import AlgebraTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/difference-of-sizes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceOfSizes.DifferenceOfSizes

theorem difference_of_sizes (A : ℝ) (B : ℝ) :
    abs A - abs B ≤ abs (A - B) := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : abs (A - B + B) ≤ abs (A - B) + abs B := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)) | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)); parley_side)
  -- 2. substitute
  have s2 : abs A ≤ abs (A - B) + abs B := by
    have c1 : A - B + B = A := by parley_ring
    have row1 : abs A ≤ abs (A - B) + abs B := by parley_subst_at c1 s1
    exact row1
  -- 3. inequalities
  have s3 : abs A - abs B ≤ abs (A - B) := by parley_order
  all_goals exact s3

end Parley.Proofs.Setmm.DifferenceOfSizes.DifferenceOfSizes
