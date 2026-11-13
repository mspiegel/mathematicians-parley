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
public import Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.QuotientIsIdentity

theorem quotient_is_identity {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a * b⁻¹ = (1 : G) ↔ a = b) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:quotient-times-divisor, from H2, H3
    have s1 : a * b⁻¹ * b = a := by exact (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) (Set.mem_univ _) (b := b) (Set.mem_univ _))
    -- 2. substitute a·b⁻¹ = e (D1) into line 1
    have s2 : (1 : G) * b = a := by parley_subst_at hD1 s1
    -- 3. calculation
    calc a = (1 : G) * b := by exact s2.symm
      _ = b := by exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) (Set.mem_univ _))
  · skip
    intro hD2
    -- 4. calculation
    calc a * b⁻¹ = b * b⁻¹ := by parley_subst hD2
      _ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) (Set.mem_univ _))

end Parley.Proofs.Setmm.GroupCancellation.QuotientIsIdentity
