module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/there-is-no.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ThereIsNo.ThereIsNoHalfInteger

theorem there_is_no_half_integer :
    ¬ (∃ x : ℤ, 2 * x = 1) := by
  -- 1. contradiction
  intro hS
  -- 1.1. obtain x from S
  obtain ⟨x, s1_1⟩ := hS
  -- 1.2. restate 1.1
  have s1_2 : 1 = 2 * x := by exact s1_1.symm
  -- 1.3. def:even n := 1, from 1.2
  have s1_3 : Even (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨x, s1_2⟩
  -- 1.4. mun:not-both n := 1, from 1.3
  have s1_4 : ¬ Odd (1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_3)
  -- 1.5. arithmetic
  have s1_5 : Odd (1 : ℤ) := by parley_arith
  exact s1_4 s1_5

end Parley.Tests.Notations.ThereIsNo.ThereIsNoHalfInteger
