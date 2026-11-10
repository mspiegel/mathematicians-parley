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
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.LeftCancellation

theorem left_cancellation {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) (g : G) (hH4 : g ∈ (Set.univ : Set G)) :
    (g * a = g * b ↔ a = b) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. axi:group-inverse-closed a := g, from H4
    have s1 : g⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4)
    -- 2. thm:the-left-inverse a := g, from H4
    have s2 : g⁻¹ * g = (1 : G) := by exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4)
    -- 3. axi:group-associative a := g⁻¹, b := g, c := a, from H2, H4, 1
    have s3 : g⁻¹ * g * a = g⁻¹ * (g * a) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2)
    -- 4. axi:group-associative a := g⁻¹, b := g, c := b, from H3, H4, 1
    have s4 : g⁻¹ * g * b = g⁻¹ * (g * b) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3)
    -- 5. substitute g⁻¹·g = e (line 2) into line 3
    have s5 : (1 : G) * a = g⁻¹ * (g * a) := by parley_subst_at s2 s3
    -- 6. substitute g·a = g·b (D1) into line 5
    have s6 : (1 : G) * a = g⁻¹ * (g * b) := by parley_subst_at hD1 s5
    -- 7. substitute g⁻¹·g = e (line 2) into line 4
    have s7 : (1 : G) * b = g⁻¹ * (g * b) := by parley_subst_at s2 s4
    -- 8. calculation
    calc a = (1 : G) * a := (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2).symm
      _ = g⁻¹ * (g * b) := by exact s6
      _ = (1 : G) * b := by exact s7.symm
      _ = b := by exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3)
  · skip
    intro hD2
    -- 9. substitute a = b (D2)
    parley_subst hD2

end Parley.Proofs.Setmm.GroupCancellation.LeftCancellation
