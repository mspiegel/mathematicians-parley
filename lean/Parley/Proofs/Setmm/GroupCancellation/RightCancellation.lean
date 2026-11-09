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

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.RightCancellation

theorem right_cancellation {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) (g : G) (hH4 : g ∈ (Set.univ : Set G)) :
    (a * g = b * g ↔ a = b) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. axi:group-inverse-closed a := g, from H4
    have s1 : g⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4)
    -- 2. axi:group-inverse a := g, from H4
    have s2 : g * g⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := g) hH4)
    -- 3. axi:group-associative b := g, c := g⁻¹, from H2, H4, 1
    have s3 : a * g * g⁻¹ = a * (g * g⁻¹) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := g) (c := g⁻¹) hH2 hH4 s1)
    -- 4. substitute g·g⁻¹ = e (line 2) into line 3
    have s4 : a * g * g⁻¹ = a * (1 : G) := by parley_subst_at s2 s3
    -- 5. substitute a·g = b·g (D1) into line 4
    have s5 : b * g * g⁻¹ = a * (1 : G) := by parley_subst_at hD1 s4
    -- 6. axi:group-associative a := b, b := g, c := g⁻¹, from H3, H4, 1
    have s6 : b * g * g⁻¹ = b * (g * g⁻¹) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := g) (c := g⁻¹) hH3 hH4 s1)
    -- 7. substitute g·g⁻¹ = e (line 2) into line 6
    have s7 : b * g * g⁻¹ = b * (1 : G) := by parley_subst_at s2 s6
    -- 8. calculation
    calc a = a * (1 : G) := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2).symm
      _ = b * g * g⁻¹ := by exact s5.symm
      _ = b * (1 : G) := by exact s7
      _ = b := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) hH3)
  · skip
    intro hD2
    -- 9. substitute a = b (D2)
    parley_subst hD2

end Parley.Proofs.Setmm.GroupCancellation.RightCancellation
