module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-witness-the-checker-read.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AWitnessTheCheckerRead.ASetMemberBesideAnEquation

theorem a_set_member_beside_an_equation (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : a ≠ b ∧ c = a + b) :
    c ∈ {u : ℤ | ∃ x : ℤ, ∃ y : ℤ, x ≠ y ∧ u = x + y} := by
  set S : Set ℤ := {u : ℤ | ∃ x : ℤ, ∃ y : ℤ, x ≠ y ∧ u = x + y} with hD1
  -- 1. def:set-builder u := c, from D1, H4
  have hI : c ∈ {t : ℤ | ∃ a : ℤ, ∃ b : ℤ, a ≠ b ∧ t = a + b} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun u : ℤ => ∃ x : ℤ, ∃ y : ℤ, x ≠ y ∧ u = x + y)) (X := (Set.univ : Set ℤ)) (u := c))).mpr ⟨by parley_set_side, a, b, hH4.1, hH4.2⟩)
  exact hI

end Parley.Tests.Elaborator.AWitnessTheCheckerRead.ASetMemberBesideAnEquation
