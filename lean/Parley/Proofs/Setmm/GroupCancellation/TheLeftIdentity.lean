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
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity

theorem the_left_identity {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    (1 : G) * a = a := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2); parley_set_side)
  -- 2. axi:group-associative b := a⁻¹, c := a, from H2, 1
  have s2 : a * a⁻¹ * a = a * (a⁻¹ * a) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s1 hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s1 hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s1 hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s1 hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s1 hH2); parley_set_side)
  -- 3. substitute
  have s3 : a * a⁻¹ * a = a * (1 : G) := by
    have c1 : a⁻¹ * a = (1 : G) := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := a) hH2) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := a) hH2)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := a) hH2) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := a) hH2) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := a) hH2); parley_set_side)
    have row1 : a * a⁻¹ * a = a * (1 : G) := by parley_subst_at c1 s2
    exact row1
  -- 4. substitute
  have s4 : (1 : G) * a = a * (1 : G) := by
    have c1 : a * a⁻¹ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2); parley_set_side)
    have row1 : (1 : G) * a = a * (1 : G) := by parley_subst_at c1 s3
    exact row1
  -- 5. calculation
  have s5 : (1 : G) * a = a := by
    calc (1 : G) * a = a * (1 : G) := by parley_set_side
      _ = a := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2); parley_set_side)
  all_goals exact s5

end Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity
