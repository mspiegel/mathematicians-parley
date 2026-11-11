module

public import ArithTactics
public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.EvenInTheEvens

theorem even_in_the_evens :
    (4 : ℤ) ∈ {x : ℤ | 0 < x ∧ Even x} := by
  set E : Set ℤ := {x : ℤ | 0 < x ∧ Even x} with hD1
  -- 1. arithmetic
  have s1 : Even (4 : ℤ) := by parley_arith
  -- 2. def:set-builder u := 4, from D1, 1
  have hI : (4 : ℤ) ∈ {t : ℤ | 0 < t ∧ Even t} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => Even x)) (X := {n : ℤ | 0 < n}) (u := (4 : ℤ)))).mpr ⟨by parley_set_side, s1⟩)
  exact hI

end Parley.Tests.Notations.Sets.EvenInTheEvens
