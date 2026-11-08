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
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseOfInverse

theorem group_inverse_of_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    a⁻¹⁻¹ = a := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
  -- 2. axi:group-inverse-closed a := a⁻¹, from 1
  have s2 : a⁻¹⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹) s1)
  -- 3. calculation
  have s3 : a⁻¹ * a⁻¹⁻¹ = a⁻¹ * a := by
    calc a⁻¹ * a⁻¹⁻¹ = (1 : G) := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹) s1)
      _ = a⁻¹ * a := (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) hH2).symm
  -- 4. thm:group-cancel a := (a⁻¹)⁻¹, b := a, g := a⁻¹, from H2, 1, 2, 3
  exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹⁻¹) (b := a) (g := a⁻¹) s2 hH2 s1 s3)

end Parley.Proofs.Setmm.GroupInverses.GroupInverseOfInverse
