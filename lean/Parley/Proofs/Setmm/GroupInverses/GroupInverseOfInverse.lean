module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseOfInverse

theorem group_inverse_of_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    a⁻¹⁻¹ = a := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 2. axi:group-inverse-closed a := a⁻¹, from 1
  have s2 : a⁻¹⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) (by parley_set_side)); parley_set_side)
  -- 3. calculation
  have s3 : a⁻¹ * a⁻¹⁻¹ = a⁻¹ * a := by
    calc a⁻¹ * a⁻¹⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) (by parley_set_side)); parley_set_side)
      _ = a⁻¹ * a := by first | exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 4. thm:group-cancel a := (a⁻¹)⁻¹, b := a, g := a⁻¹, from H2, 1, 2, 3
  have s4 : a⁻¹⁻¹ = a := by first | exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupInverses.GroupInverseOfInverse
