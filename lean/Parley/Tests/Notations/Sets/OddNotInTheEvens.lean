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

namespace Parley.Tests.Notations.Sets.OddNotInTheEvens

theorem odd_not_in_the_evens :
    ¬ (3 : ℤ) ∈ {x : ℤ | 0 < x ∧ Even x} := by
  set E : Set ℤ := {x : ℤ | 0 < x ∧ Even x} with hD1
  -- 1. arithmetic
  have s1 : ¬ Even (3 : ℤ) := by parley_arith
  -- 2. contradiction
  intro hS
  -- 2.1. def:set-builder u := 3, from D1, S
  have s2_1 : Even (3 : ℤ) := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    have hI : Even (3 : ℤ) := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => Even x)) (X := {n : ℤ | 0 < n}) (u := (3 : ℤ)))).mp hS).2)
    exact hI
  exact s1 s2_1

end Parley.Tests.Notations.Sets.OddNotInTheEvens
