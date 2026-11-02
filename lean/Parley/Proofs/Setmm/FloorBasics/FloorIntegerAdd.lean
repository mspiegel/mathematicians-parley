module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Setmm.FloorBasics.FloorAddInteger

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd

theorem floor_integer_add (N : ℤ) (A : ℝ) :
    ⌊(N : ℝ) + A⌋ = N + ⌊A⌋ := by
  -- 1. mun:floor-integer x := A
  -- 2. algebra
  have s2 : (N : ℝ) + A = A + (N : ℝ) := by parley_ring
  -- 3. calculation
  have s3 : ⌊(N : ℝ) + A⌋ = N + ⌊A⌋ := by
    calc ⌊(N : ℝ) + A⌋ = ⌊A + (N : ℝ)⌋ := by parley_subst s2
      _ = ⌊A⌋ + N := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N)) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N)) | exact_mod_cast ((Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N))).symm | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N)); qify; linear_combination (norm := parley_norm) h)
      _ = N + ⌊A⌋ := by parley_ring
  all_goals parley_side

end Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd
