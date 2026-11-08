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

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupInverseByRight

theorem group_inverse_by_right {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a⁻¹ = b ↔ a * b = (1 : G)) := by
  -- 1. axi:group-inverse-closed, from H2
  have s1 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
  -- 2. axi:group-inverse, from H2
  have s2 : a * a⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)
  -- 3. both directions
  constructor
  · skip
    intro hD1
    -- 3.1. substitute a⁻¹ = b (D1) into line 2
    parley_subst_at hD1 s2
  · skip
    intro hD2
    -- 3.2. calculation
    have s3_2 : a * a⁻¹ = a * b := by
      calc a * a⁻¹ = (1 : G) := by parley_set_side
        _ = a * b := by parley_set_side
    -- 3.3. thm:group-cancel a := a⁻¹, g := a, from H2, H3, 1, 3.2
    exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a⁻¹) (b := b) (g := a) s1 hH3 hH2 s3_2)

end Parley.Proofs.Setmm.GroupInverses.GroupInverseByRight
