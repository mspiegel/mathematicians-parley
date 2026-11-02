module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupCancelInverse

theorem group_cancel_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    a * (a⁻¹ * b) = b := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 2. axi:group-inverse, from H2
  have s2 : a * a⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 3. calculation
  have s3 : a * (a⁻¹ * b) = b := by
    calc a * (a⁻¹ * b) = a * a⁻¹ * b := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
      _ = (1 : G) * b := by parley_subst s2
      _ = b := by first | exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := b) (by parley_set_side)) | exact ((Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := b) (by parley_set_side))).symm | simpa using (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := b) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := b) (by parley_set_side)) | (have h := (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := b) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupInverses.GroupCancelInverse
