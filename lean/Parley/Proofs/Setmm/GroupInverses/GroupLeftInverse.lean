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
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

theorem group_left_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    a⁻¹ * a = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  set b : G := a⁻¹ with hD1
  set c : G := b⁻¹ with hD2
  -- 2. axi:group-inverse-closed, from D1, H2
  have s2 : b ∈ (Set.univ : Set G) := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)
  -- 3. axi:group-inverse-closed a := b, from D2, 2
  have s3 : c ∈ (Set.univ : Set G) := by
    try simp only [hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2)
  -- 4. axi:group-closed a := b, b := a, from H2, 2
  have s4 : b * a ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2)
  -- 5. axi:group-closed a := b, b := c, from 2, 3
  have s5 : b * c ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3)
  -- 6. axi:group-inverse a := b, from D2, 2
  have s6 : b * c = (1 : G) := by
    try simp only [hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2)
  -- 7. axi:group-inverse, from D1, H2
  have s7 : a * b = (1 : G) := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)
  -- 8. calculation
  have s8 : a * (b * c) = (1 : G) * c := by
    calc a * (b * c) = a * b * c := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3).symm
      _ = (1 : G) * c := by parley_subst s7
  -- 9. axi:group-identity a := b, from 2
  have s9 : b * (1 : G) = b := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2)
  -- 10. calculation
  calc a⁻¹ * a = b * a := by simp (disch := omega) only [hD1]
    _ = b * a * (1 : G) := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4).symm
    _ = b * a * (b * c) := by parley_subst s6
    _ = b * (a * (b * c)) := by exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5)
    _ = b * ((1 : G) * c) := by parley_subst s8
    _ = b * (1 : G) * c := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3).symm
    _ = b * c := by parley_subst s9
    _ = (1 : G) := by exact s6

end Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse
