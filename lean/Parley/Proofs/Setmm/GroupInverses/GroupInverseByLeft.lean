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
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity
public import Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseByLeft

theorem group_inverse_by_left {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a⁻¹ = b ↔ b * a = (1 : G)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:group-left-inverse, from H2
    have s1 : a⁻¹ * a = (1 : G) := by exact (Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse.group_left_inverse (G := G) (a := a) hH2)
    -- 2. substitute a⁻¹ = b (D1) into line 1
    parley_subst_at hD1 s1
  · skip
    intro hD2
    -- 3. axi:group-inverse-closed, from H2
    have s3 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
    -- 4. axi:group-inverse, from H2
    have s4 : a * a⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)
    -- 5. calculation
    calc a⁻¹ = (1 : G) * a⁻¹ := (Parley.Proofs.Setmm.GroupInverses.GroupLeftIdentity.group_left_identity (G := G) (a := a⁻¹) s3).symm
      _ = b * a * a⁻¹ := by parley_subst hD2
      _ = b * (a * a⁻¹) := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := a⁻¹) hH3 hH2 s3)
      _ = b * (1 : G) := by parley_subst s4
      _ = b := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) hH3)

end Parley.Proofs.Setmm.GroupInverses.GroupInverseByLeft
