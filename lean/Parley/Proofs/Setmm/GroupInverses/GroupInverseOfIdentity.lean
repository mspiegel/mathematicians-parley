module

public import SetTactics
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
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseOfIdentity

theorem group_inverse_of_identity {G : Type*} [Group G] :
    (1 : G)⁻¹ = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  -- 2. axi:group-inverse-closed a := e, from 1
  have s2 : (1 : G)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) s1)
  -- 3. calculation
  have s3 : (1 : G)⁻¹ = (1 : G) := by
    calc (1 : G)⁻¹ = (1 : G) * (1 : G)⁻¹ := by first | exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) s2) | exact ((Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) s2)).symm | simpa using (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) s2) | exact_mod_cast (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) s2) | (have h := (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) s2); parley_set_side)
      _ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Setmm.GroupInverses.GroupInverseOfIdentity
