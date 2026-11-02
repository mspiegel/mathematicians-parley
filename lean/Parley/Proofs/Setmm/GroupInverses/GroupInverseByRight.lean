module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseByRight

theorem group_inverse_by_right {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a⁻¹ = b ↔ a * b = (1 : G)) := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 2. axi:group-inverse, from H2
  have s2 : a * a⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (by parley_set_side)); parley_set_side)
  -- 3. both directions
  have s3 : a⁻¹ = b ↔ a * b = (1 : G) := by
    constructor
    · skip
      intro hD1
      -- 3.1. substitute a⁻¹ = b (D1) into line 2
      have s3_1 : a * b = (1 : G) := by parley_subst_at hD1 s2
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3.2. calculation
      have s3_2 : a * a⁻¹ = a * b := by
        calc a * a⁻¹ = (1 : G) := by parley_set_side
          _ = a * b := by parley_set_side
      -- 3.3. thm:group-cancel a := a⁻¹, g := a, from H2, H3, 1, 3.2
      have s3_3 : a⁻¹ = b := by first | exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupInverses.GroupInverseByRight
