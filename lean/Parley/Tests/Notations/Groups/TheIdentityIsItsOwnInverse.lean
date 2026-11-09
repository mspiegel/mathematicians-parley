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

/-! Written from tests/notations/groups.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Groups.TheIdentityIsItsOwnInverse

theorem the_identity_is_its_own_inverse {G : Type*} [Group G] :
    (1 : G)⁻¹ = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  -- 2. axi:group-inverse-closed a := e, from 1
  have s2 : (1 : G)⁻¹ ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := (1 : G)) s1)
  -- 3. axi:group-inverse a := e, from 1
  have s3 : (1 : G) * (1 : G)⁻¹ = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := (1 : G)) s1)
  -- 4. axi:group-identity a := e, from 1
  have s4 : (1 : G) * (1 : G) = (1 : G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := (1 : G)) s1)
  -- 5. calculation
  have s5 : (1 : G) * (1 : G)⁻¹ = (1 : G) * (1 : G) := by
    calc (1 : G) * (1 : G)⁻¹ = (1 : G) := by exact s3
      _ = (1 : G) * (1 : G) := by exact s4.symm
  -- 6. thm:group-cancel a := e⁻¹, b := e, g := e, from 1, 2, 5
  exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := (1 : G)⁻¹) (b := (1 : G)) (g := (1 : G)) s2 s1 s1 s5)

end Parley.Tests.Notations.Groups.TheIdentityIsItsOwnInverse
