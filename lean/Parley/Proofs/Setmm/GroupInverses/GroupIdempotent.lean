module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupIdempotent

theorem group_idempotent {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    (a * a = a ↔ a = (1 : G)) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))
  -- 2. axi:group-identity, from H2
  have s2 : a * (1 : G) = a := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) hH2)
  -- 3. both directions
  have s3 : a * a = a ↔ a = (1 : G) := by
    constructor
    · skip
      intro hD1
      -- 3.1. calculation
      have s3_1 : a * a = a * (1 : G) := by
        calc a * a = a := by parley_set_side
          _ = a * (1 : G) := by parley_set_side
      -- 3.2. thm:group-cancel b := e, g := a, from H2, 1, 3.1
      have s3_2 : a = (1 : G) := by exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) hH2 s1 hH2 s3_1)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 3.3. calculation
      have s3_3 : a * a = a := by
        calc a * a = a * (1 : G) := by parley_subst hD2
          _ = a := by parley_set_side
      all_goals parley_set_side
  all_goals exact s3

end Parley.Proofs.Setmm.GroupInverses.GroupIdempotent
