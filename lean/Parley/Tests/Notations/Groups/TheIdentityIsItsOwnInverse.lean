module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from tests/notations/groups.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Groups.TheIdentityIsItsOwnInverse

theorem the_identity_is_its_own_inverse {G : Type*} [Group G] :
    (1 : G)⁻¹ = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)); parley_set_side)
  -- 2. axi:group-inverse-closed a := e, from 1
  have s2 : (1 : G)⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (by parley_set_side)); parley_set_side)
  -- 3. axi:group-inverse a := e, from 1
  have s3 : (1 : G) * (1 : G)⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (by parley_set_side)); parley_set_side)
  -- 4. axi:group-identity a := e, from 1
  have s4 : (1 : G) * (1 : G) = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) (by parley_set_side)); parley_set_side)
  -- 5. calculation
  have s5 : (1 : G) * (1 : G)⁻¹ = (1 : G) * (1 : G) := by
    calc (1 : G) * (1 : G)⁻¹ = (1 : G) := by parley_set_side
      _ = (1 : G) * (1 : G) := by parley_set_side
  -- 6. thm:group-cancel a := e⁻¹, b := e, g := e, from 1, 2, 5
  have s6 : (1 : G)⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Tests.Notations.Groups.TheIdentityIsItsOwnInverse
