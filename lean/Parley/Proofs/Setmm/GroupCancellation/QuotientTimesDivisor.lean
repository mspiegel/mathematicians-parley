module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor

theorem quotient_times_divisor {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    a * b⁻¹ * b = a := by
  -- 1. axi:group-inverse-closed a := b, from H3
  have s1 : b⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3); parley_set_side)
  -- 2. axi:group-associative b := b⁻¹, c := b, from H2, H3, 1
  have s2 : a * b⁻¹ * b = a * (b⁻¹ * b) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) hH2 s1 hH3) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) hH2 s1 hH3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) hH2 s1 hH3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) hH2 s1 hH3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b⁻¹) (c := b) hH2 s1 hH3); parley_set_side)
  -- 3. substitute
  have s3 : a * b⁻¹ * b = a * (1 : G) := by
    have c1 : b⁻¹ * b = (1 : G) := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) hH3) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) hH3)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) hH3) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) hH3) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := b) hH3); parley_set_side)
    have row1 : a * b⁻¹ * b = a * (1 : G) := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : a * b⁻¹ * b = a := by
    calc a * b⁻¹ * b = a * (1 : G) := by parley_set_side
      _ = a := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2); parley_set_side)
  all_goals exact s4

end Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor
