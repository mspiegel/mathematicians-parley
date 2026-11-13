module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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
  have s2 : (1 : G)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) (Set.mem_univ _))
  -- 3. calculation
  calc (1 : G)⁻¹ = (1 : G) * (1 : G)⁻¹ := (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := (1 : G)⁻¹) (Set.mem_univ _)).symm
    _ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) (Set.mem_univ _))

end Parley.Proofs.Setmm.GroupInverses.GroupInverseOfIdentity
