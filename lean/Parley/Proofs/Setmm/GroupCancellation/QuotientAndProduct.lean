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
public import Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.QuotientAndProduct

theorem quotient_and_product {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) (c : G) (hH4 : c ∈ (Set.univ : Set G)) :
    (a * b⁻¹ = c ↔ c * b = a) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:quotient-times-divisor, from H2, H3
    have s1 : a * b⁻¹ * b = a := by exact (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3)
    -- 2. substitute a·b⁻¹ = c (D1) into line 1
    parley_subst_at hD1 s1
  · skip
    intro hD2
    -- 3. axi:group-inverse-closed a := b, from H3
    have s3 : b⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) hH3)
    -- 4. axi:group-associative a := c, c := b⁻¹, from H3, H4, 3
    have s4 : c * b * b⁻¹ = c * (b * b⁻¹) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := c) (b := b) (c := b⁻¹) hH4 hH3 s3)
    -- 5. substitute
    have s5 : c * b * b⁻¹ = c * (1 : G) := by
      have c1 : b * b⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3)
      have row1 : c * b * b⁻¹ = c * (1 : G) := by parley_subst_at c1 s4
      exact row1
    -- 6. calculation
    calc a * b⁻¹ = c * b * b⁻¹ := by parley_subst hD2
      _ = c * (1 : G) := by exact s5
      _ = c := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := c) hH4)

end Parley.Proofs.Setmm.GroupCancellation.QuotientAndProduct
