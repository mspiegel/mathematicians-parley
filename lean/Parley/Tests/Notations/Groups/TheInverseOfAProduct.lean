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

/-! Written from tests/notations/groups.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Groups.TheInverseOfAProduct

theorem the_inverse_of_a_product {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- 1. axi:group-closed, from H2, H3
  have s1 : a * b ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := a) (b := b) (Set.mem_univ _) (Set.mem_univ _))
  -- 2. axi:group-inverse-closed, from H2
  have s2 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) (Set.mem_univ _))
  -- 3. axi:group-inverse-closed a := b, from H3
  have s3 : b⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) (Set.mem_univ _))
  -- 4. axi:group-closed a := b⁻¹, b := a⁻¹, from 2, 3
  have s4 : b⁻¹ * a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b⁻¹) (b := a⁻¹) (Set.mem_univ _) (Set.mem_univ _))
  -- 5. axi:group-inverse-closed a := a·b, from 1
  have s5 : (a * b)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a * b) (Set.mem_univ _))
  -- 6. axi:group-identity-closed
  have s6 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  -- 7. axi:group-associative c := b⁻¹·a⁻¹, from H2, H3, 4
  have s7 : a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := b⁻¹ * a⁻¹) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _))
  -- 8. axi:group-associative a := b, b := b⁻¹, c := a⁻¹, from H3, 2, 3
  have s8 : b * (b⁻¹ * a⁻¹) = b * b⁻¹ * a⁻¹ := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := b⁻¹) (c := a⁻¹) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)).symm
  -- 9. axi:group-inverse a := b, from H3
  have s9 : b * b⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) (Set.mem_univ _))
  -- 10. axi:group-associative a := a⁻¹, b := e, c := a⁻¹, from 2, 6
  have s10 : a⁻¹ * ((1 : G) * a⁻¹) = a⁻¹ * (1 : G) * a⁻¹ := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a⁻¹) (b := (1 : G)) (c := a⁻¹) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)).symm
  -- 11. axi:group-identity a := a⁻¹, from 2
  have s11 : a⁻¹ * (1 : G) = a⁻¹ := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a⁻¹) (Set.mem_univ _))
  -- 12. substitute a⁻¹·e = a⁻¹ (line 11) into line 10
  have s12 : a⁻¹ * ((1 : G) * a⁻¹) = a⁻¹ * a⁻¹ := by parley_subst_at s11 s10
  -- 13. axi:group-closed a := e, b := a⁻¹, from 2, 6
  have s13 : (1 : G) * a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := (1 : G)) (b := a⁻¹) (Set.mem_univ _) (Set.mem_univ _))
  -- 14. thm:group-cancel a := e·a⁻¹, b := a⁻¹, g := a⁻¹, from 2, 12, 13
  have s14 : (1 : G) * a⁻¹ = a⁻¹ := by exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G) * a⁻¹) (b := a⁻¹) (g := a⁻¹) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) s12)
  -- 15. substitute b·b⁻¹ = e (line 9) into line 8
  have s15 : b * (b⁻¹ * a⁻¹) = (1 : G) * a⁻¹ := by parley_subst_at s9 s8
  -- 16. substitute e·a⁻¹ = a⁻¹ (line 14) into line 15
  have s16 : b * (b⁻¹ * a⁻¹) = a⁻¹ := by parley_subst_at s14 s15
  -- 17. substitute b·(b⁻¹·a⁻¹) = a⁻¹ (line 16) into line 7
  have s17 : a * b * (b⁻¹ * a⁻¹) = a * a⁻¹ := by parley_subst_at s16 s7
  -- 18. axi:group-inverse, from H2
  have s18 : a * a⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) (Set.mem_univ _))
  -- 19. axi:group-inverse a := a·b, from 1
  have s19 : a * b * (a * b)⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a * b) (Set.mem_univ _))
  -- 20. calculation
  have s20 : a * b * (a * b)⁻¹ = a * b * (b⁻¹ * a⁻¹) := by
    calc a * b * (a * b)⁻¹ = (1 : G) := by exact s19
      _ = a * a⁻¹ := by exact s18.symm
      _ = a * b * (b⁻¹ * a⁻¹) := by exact s17.symm
  -- 21. thm:group-cancel a := (a·b)⁻¹, b := b⁻¹·a⁻¹, g := a·b, from 1, 4, 5, 20
  exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (a * b)⁻¹) (b := b⁻¹ * a⁻¹) (g := a * b) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) s20)

end Parley.Tests.Notations.Groups.TheInverseOfAProduct
