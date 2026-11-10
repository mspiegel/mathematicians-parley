module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-difference-of-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddDifferenceOfSquares.OddDifferenceOfSquares

theorem odd_difference_of_squares (n : ℤ) (hH2 : Odd n) :
    (∃ a : ℤ, ∃ b : ℤ, n = a ^ 2 - b ^ 2) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. calculation
  have s2 : n = (k + 1) ^ 2 - k ^ 2 := by
    calc n = 2 * k + 1 := by exact s1
      _ = (k + 1) ^ 2 - k ^ 2 := by parley_ring
  -- 3. exhibit, from 2
  exact ⟨k + 1, k, s2⟩

end Parley.Proofs.Hammack.OddDifferenceOfSquares.OddDifferenceOfSquares
