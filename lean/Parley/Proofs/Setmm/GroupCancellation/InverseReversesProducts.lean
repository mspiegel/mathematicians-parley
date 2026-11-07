module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupCancellation.LeftCancellation
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.InverseReversesProducts

set_option maxHeartbeats 400000 in
theorem inverse_reverses_products {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- 1. axi:group-closed, from H2, H3
  have s1 : a * b ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := a) (b := b) hH2 hH3)
  -- 2. axi:group-inverse-closed, from H2
  have s2 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
  -- 3. axi:group-inverse-closed a := b, from H3
  have s3 : b⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3)
  -- 4. axi:group-closed a := b⁻¹, b := a⁻¹, from 2, 3
  have s4 : b⁻¹ * a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b⁻¹) (b := a⁻¹) s3 s2)
  -- 5. axi:group-inverse-closed a := a·b, from 1
  have s5 : (a * b)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a * b) s1)
  -- 6. axi:group-associative a := b, b := b⁻¹, c := a⁻¹, from H3, 2, 3
  have s6 : b * b⁻¹ * a⁻¹ = b * (b⁻¹ * a⁻¹) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := b⁻¹) (c := a⁻¹) hH3 s3 s2)
  -- 7. substitute
  have s7 : (1 : G) * a⁻¹ = b * (b⁻¹ * a⁻¹) := by
    have c1 : b * b⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3)
    have row1 : (1 : G) * a⁻¹ = b * (b⁻¹ * a⁻¹) := by parley_subst_at c1 s6
    exact row1
  -- 8. calculation
  have s8 : b * (b⁻¹ * a⁻¹) = a⁻¹ := by
    calc b * (b⁻¹ * a⁻¹) = (1 : G) * a⁻¹ := by parley_set_side
      _ = a⁻¹ := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a⁻¹) s2) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a⁻¹) s2)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a⁻¹) s2) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a⁻¹) s2) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a⁻¹) s2); parley_set_side)
  -- 9. axi:group-associative c := b⁻¹·a⁻¹, from H2, H3, 4
  have s9 : a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := b⁻¹ * a⁻¹) hH2 hH3 s4)
  -- 10. substitute b·(b⁻¹·a⁻¹) = a⁻¹ (line 8) into line 9
  have s10 : a * b * (b⁻¹ * a⁻¹) = a * a⁻¹ := by parley_subst_at s8 s9
  -- 11. calculation
  have s11 : a * b * (a * b)⁻¹ = a * b * (b⁻¹ * a⁻¹) := by
    calc a * b * (a * b)⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) s1) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) s1)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) s1) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) s1) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) s1); parley_set_side)
      _ = a * a⁻¹ := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2); parley_set_side)
      _ = a * b * (b⁻¹ * a⁻¹) := by parley_set_side
  -- 12. thm:left-cancellation a := (a·b)⁻¹, b := b⁻¹·a⁻¹, g := a·b, from 1, 4, 5, 11
  have s12 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by first | exact ((Parley.Proofs.Setmm.GroupCancellation.LeftCancellation.left_cancellation (G := G) (a := (a * b)⁻¹) s5 (b := b⁻¹ * a⁻¹) s4 (g := a * b) s1)).mp (by parley_set_side) | exact (((Parley.Proofs.Setmm.GroupCancellation.LeftCancellation.left_cancellation (G := G) (a := (a * b)⁻¹) s5 (b := b⁻¹ * a⁻¹) s4 (g := a * b) s1)).mp (by parley_set_side)).symm | simpa using ((Parley.Proofs.Setmm.GroupCancellation.LeftCancellation.left_cancellation (G := G) (a := (a * b)⁻¹) s5 (b := b⁻¹ * a⁻¹) s4 (g := a * b) s1)).mp (by parley_set_side) | exact_mod_cast ((Parley.Proofs.Setmm.GroupCancellation.LeftCancellation.left_cancellation (G := G) (a := (a * b)⁻¹) s5 (b := b⁻¹ * a⁻¹) s4 (g := a * b) s1)).mp (by parley_set_side) | (have h := ((Parley.Proofs.Setmm.GroupCancellation.LeftCancellation.left_cancellation (G := G) (a := (a * b)⁻¹) s5 (b := b⁻¹ * a⁻¹) s4 (g := a * b) s1)).mp (by parley_set_side); parley_set_side)
  all_goals exact s12

end Parley.Proofs.Setmm.GroupCancellation.InverseReversesProducts
