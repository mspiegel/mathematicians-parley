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

namespace Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

set_option maxHeartbeats 400000 in
theorem the_left_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    a⁻¹ * a = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  -- 2. axi:group-inverse-closed, from H2
  have s2 : a⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
  -- 3. axi:group-closed a := a⁻¹, b := a, from H2, 2
  have s3 : a⁻¹ * a ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := a⁻¹) (b := a) s2 hH2)
  -- 4. axi:group-inverse-closed a := a⁻¹·a, from 3
  have s4 : (a⁻¹ * a)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a⁻¹ * a) s3)
  -- 5. axi:group-associative a := a⁻¹, b := a, c := a⁻¹·a, from H2, 2, 3
  have s5 : a⁻¹ * a * (a⁻¹ * a) = a⁻¹ * (a * (a⁻¹ * a)) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a⁻¹) (b := a) (c := a⁻¹ * a) s2 hH2 s3)
  -- 6. axi:group-associative b := a⁻¹, c := a, from H2, 2
  have s6 : a * (a⁻¹ * a) = a * a⁻¹ * a := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := a⁻¹) (c := a) hH2 s2 hH2).symm
  -- 7. substitute
  have s7 : a * (a⁻¹ * a) = (1 : G) * a := by
    have c1 : a * a⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)
    have row1 : a * (a⁻¹ * a) = (1 : G) * a := by parley_subst_at c1 s6
    exact row1
  -- 8. axi:group-associative a := a⁻¹, b := e, c := a, from H2, 1, 2
  have s8 : a⁻¹ * ((1 : G) * a) = a⁻¹ * (1 : G) * a := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a⁻¹) (b := (1 : G)) (c := a) s2 s1 hH2).symm
  -- 9. substitute
  have s9 : a⁻¹ * ((1 : G) * a) = a⁻¹ * a := by
    have c1 : a⁻¹ * (1 : G) = a⁻¹ := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a⁻¹) s2)
    have row1 : a⁻¹ * ((1 : G) * a) = a⁻¹ * a := by parley_subst_at c1 s8
    exact row1
  -- 10. substitute a·(a⁻¹·a) = e·a (line 7) into line 5
  have s10 : a⁻¹ * a * (a⁻¹ * a) = a⁻¹ * ((1 : G) * a) := by parley_subst_at s7 s5
  -- 11. calculation
  have s11 : a⁻¹ * a * (a⁻¹ * a) = a⁻¹ * a := by
    calc a⁻¹ * a * (a⁻¹ * a) = a⁻¹ * ((1 : G) * a) := by exact s10
      _ = a⁻¹ * a := by exact s9
  -- 12. axi:group-associative a := a⁻¹·a, b := a⁻¹·a, c := (a⁻¹·a)⁻¹, from 3, 4
  have s12 : a⁻¹ * a * (a⁻¹ * a) * (a⁻¹ * a)⁻¹ = a⁻¹ * a * (a⁻¹ * a * (a⁻¹ * a)⁻¹) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a⁻¹ * a) (b := a⁻¹ * a) (c := (a⁻¹ * a)⁻¹) s3 s3 s4)
  -- 13. substitute (a⁻¹·a)·(a⁻¹·a) = a⁻¹·a (line 11) into line 12
  have s13 : a⁻¹ * a * (a⁻¹ * a)⁻¹ = a⁻¹ * a * (a⁻¹ * a * (a⁻¹ * a)⁻¹) := by parley_subst_at s11 s12
  -- 14. substitute
  have s14 : (1 : G) = a⁻¹ * a * (1 : G) := by
    have c1 : a⁻¹ * a * (a⁻¹ * a)⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a⁻¹ * a) s3)
    have row1 : (1 : G) = a⁻¹ * a * (1 : G) := by parley_subst_at c1 s13
    exact row1
  -- 15. calculation
  calc a⁻¹ * a = a⁻¹ * a * (1 : G) := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a⁻¹ * a) s3).symm
    _ = (1 : G) := by exact s14.symm

end Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse
