module

public import SetTactics
public import SubstTactics
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
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity

theorem group_left_identity {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    (1 : G) * a = a := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (Set.mem_univ _))
  -- 2. axi:group-inverse, from H2
  have s2 : a * a⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (Set.mem_univ _))
  -- 3. thm:group-left-inverse, from H2
  have s3 : a⁻¹ * a = (1 : G) := by exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) (Set.mem_univ _))
  -- 4. calculation
  calc (1 : G) * a = a * a⁻¹ * a := by parley_subst s2
    _ = a * (a⁻¹ * a) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _))
    _ = a * (1 : G) := by parley_subst s3
    _ = a := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (Set.mem_univ _))

end Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity
