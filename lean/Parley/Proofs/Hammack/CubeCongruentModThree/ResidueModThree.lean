module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/cube-congruent-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

theorem residue_mod_three (r : ℕ) (hH2 : (r : ℤ) < 3) :
    (((r : ℤ) = 0 ∨ (r : ℤ) = 1) ∨ (r : ℤ) = 2) := by
  -- 1. mun:range-from-bounds, from H2
  have s1 : (r : ℤ) ∈ Finset.Icc (0 : ℤ) (3 - 1 : ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := r) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := r) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := r) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := r) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := r) (by parley_side)); parley_side)
  -- 2. inspection, from 1
  have s2 : ((r : ℤ) = 0 ∨ (r : ℤ) = 1) ∨ (r : ℤ) = 2 := by parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree
