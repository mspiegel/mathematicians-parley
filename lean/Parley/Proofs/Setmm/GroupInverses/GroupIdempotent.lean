module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupIdempotent

theorem group_idempotent {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    (a * a = a ↔ a = (1 : G)) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)); parley_set_side)
  -- 2. axi:group-identity, from H2
  have s2 : a * (1 : G) = a := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 3. both directions
  have s3 : a * a = a ↔ a = (1 : G) := by
    constructor
    · skip
      intro hD1
      -- 3.1. calculation
      have s3_1 : a * a = a * (1 : G) := by
        calc a * a = a := by parley_set_side
          _ = a * (1 : G) := by parley_set_side
      -- 3.2. thm:group-cancel b := e, g := a, from H2, 1, 3.1
      have s3_2 : a = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3.3. calculation
      have s3_3 : a * a = a := by
        calc a * a = a * (1 : G) := by parley_subst hD2
          _ = a := by parley_set_side
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupInverses.GroupIdempotent
