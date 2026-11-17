module

public import ZF
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/halmos/intersection-exists.proof by parley build lean. -/

public section

namespace Parley.Proofs.Halmos.IntersectionExists.IntersectionExists

theorem intersection_exists {α : Type*} [Nonempty α] [LeanBridges.ZF.Sets α] (A : Set α) (B : Set α) (hB_set : LeanBridges.ZF.IsSet B) (hH2 : LeanBridges.ZF.IsSet A) :
    LeanBridges.ZF.IsSet (A ∩ B) := by
  -- 1. proof
  have s1 : ∀ x ∈ {t ∈ A | t ∈ B}, x ∈ A ∩ B := by
    intro x hK1
    -- 1.1. def:set-builder X := A, from K1
    have s1_1 : x ∈ A ∧ x ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : α => t ∈ B)) (X := A) (u := x))).mp hK1
    -- 1.2. def:intersection Y := A, Z := B, from 1.1
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mpr ⟨s1_1.1, s1_1.2⟩
  -- 2. proof
  have s2 : ∀ x ∈ A ∩ B, x ∈ {t ∈ A | t ∈ B} := by
    intro x hK2
    -- 2.1. def:intersection Y := A, Z := B, from K2
    have s2_1 : x ∈ A ∧ x ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := x))).mp hK2
    -- 2.2. def:set-builder X := A, from 2.1
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun t : α => t ∈ B)) (X := A) (u := x))).mpr ⟨s2_1.1, s2_1.2⟩
  -- 3. axi:separation X := A, from H2
  have s3 : LeanBridges.ZF.IsSet {t ∈ A | t ∈ B} := by exact (Parley.Items.Stdlib.Sets.axi_separation (P := (fun t : α => t ∈ B)) (X := A) hH2)
  -- 4. substitute
  have c1 : {t ∈ A | t ∈ B} = A ∩ B := by exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := {t ∈ A | t ∈ B}) (Y := A ∩ B) s1 s2)
  have row1 : LeanBridges.ZF.IsSet (A ∩ B) := Eq.subst (motive := (fun u : Set α => LeanBridges.ZF.IsSet u)) c1 s3
  exact row1

end Parley.Proofs.Halmos.IntersectionExists.IntersectionExists
