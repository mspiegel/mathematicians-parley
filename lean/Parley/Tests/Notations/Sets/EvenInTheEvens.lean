module

public import ArithTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
  exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => Even x)) (X := {n : ℤ | 0 < n}) (u := (4 : ℤ)))).mpr ⟨by norm_num, s1⟩

end Parley.Tests.Notations.Sets.EvenInTheEvens
