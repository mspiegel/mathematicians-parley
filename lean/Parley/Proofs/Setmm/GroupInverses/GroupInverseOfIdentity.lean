module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseOfIdentity

theorem group_inverse_of_identity {G : Type*} [Group G] :
    (1 : G)⁻¹ = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)); parley_set_side)
  -- 2. axi:group-inverse-closed a := e, from 1
  have s2 : (1 : G)⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)); parley_set_side)
  -- 3. calculation
  have s3 : (1 : G)⁻¹ = (1 : G) := by
    calc (1 : G)⁻¹ = (1 : G) * (1 : G)⁻¹ := by first | exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (by parley_set_side)) | exact ((Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (by parley_set_side))).symm | simpa using (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (by parley_set_side)) | (have h := (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (by parley_set_side)); parley_set_side)
      _ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupInverses.GroupInverseOfIdentity
