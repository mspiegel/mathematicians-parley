module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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
  have s2 : a * (1 : G) = a := by exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := a) (Set.mem_univ _))
  -- 3. both directions
  constructor
  · skip
    intro hD1
    -- 3.1. calculation
    have s3_1 : a * a = a * (1 : G) := by
      calc a * a = a := hD1
        _ = a * (1 : G) := s2.symm
    -- 3.2. thm:group-cancel b := e, g := a, from H2, 1, 3.1
    exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := a) (b := (1 : G)) (g := a) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) s3_1)
  · skip
    intro hD2
    -- 3.3. calculation
    calc a * a = a * (1 : G) := by parley_subst hD2
      _ = a := s2

end Parley.Proofs.Setmm.GroupInverses.GroupIdempotent
