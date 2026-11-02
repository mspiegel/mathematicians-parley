module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor

theorem quotient_times_divisor {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    a * b⁻¹ * b = a := by
  -- 1. axi:group-inverse-closed a := b, from H3
  have s1 : b⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (by parley_set_side)); parley_set_side)
  -- 2. axi:group-associative b := b⁻¹, c := b, from H2, H3, 1
  have s2 : a * b⁻¹ * b = a * (b⁻¹ * b) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 3. substitute
  have s3 : a * b⁻¹ * b = a * (1 : G) := by
    have c1 : b⁻¹ * b = (1 : G) := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) (by parley_set_side)) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) (by parley_set_side))).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) (by parley_set_side)) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) (by parley_set_side)); parley_set_side)
    have row1 : a * b⁻¹ * b = a * (1 : G) := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : a * b⁻¹ * b = a := by
    calc a * b⁻¹ * b = a * (1 : G) := by parley_set_side
      _ = a := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor
