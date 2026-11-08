module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare

/-! Written from tests/docs/syntax.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Syntax.EvenSquare

theorem even_square (n : ℤ) (hH2 : Even (n ^ 2)) :
    Even n := by
  -- 1. contradiction
  have s1 : ¬ Odd n := by
    intro hS
    -- 1.1. thm:odd-square, from S
    have s1_1 : Odd (n ^ 2) := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) hS)
    -- 1.2. mun:not-both n := n², from H2
    have s1_2 : ¬ Odd (n ^ 2) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) hH2)
    exact s1_2 s1_1
  -- 2. mun:even-or-odd
  have s2 : Even n ∨ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 3. mun:disjunctive-syllogism P := n is even, Q := n is odd, from 1, 2
  exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) s2 s1)

end Parley.Tests.Docs.Syntax.EvenSquare
