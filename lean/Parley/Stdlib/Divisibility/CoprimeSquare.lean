module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Stdlib.Divisibility.CoprimeSquarePart

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CoprimeSquare

theorem coprime_square (s : ℤ) (hH1 : 0 < s) (t : ℤ) (hH2 : 0 < t) (w : ℤ) (hH3 : 0 < w) (hH4 : (Int.gcd s t : ℤ) = 1) (hH5 : w ^ 2 = s * t) :
    s = (Int.gcd s w : ℤ) ^ 2 ∧ t = (Int.gcd t w : ℤ) ^ 2 := by
  -- 1. mun:coprime-square-part, from H4, H5
  have s1 : s = (Int.gcd s w : ℤ) ^ 2 := by exact (Parley.Stdlib.Divisibility.CoprimeSquarePart.coprime_square_part (s := s) hH1 (t := t) hH2 (w := w) hH3 hH4 (by parley_side))
  -- 2. mun:gcd-commutes a := t, b := s
  have s2 : (Int.gcd t s : ℤ) = (Int.gcd s t : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := t) (b := s))
  -- 3. transitivity, from 2, H4
  have s3 : (Int.gcd t s : ℤ) = 1 := by parley_side
  -- 4. algebra, from H5
  have s4 : w ^ 2 = t * s := by linear_combination (norm := parley_norm) hH5
  -- 5. mun:coprime-square-part s := t, t := s, from 3, 4
  have s5 : t = (Int.gcd t w : ℤ) ^ 2 := by exact (Parley.Stdlib.Divisibility.CoprimeSquarePart.coprime_square_part (s := t) hH2 (t := s) hH1 (w := w) hH3 s3 (by parley_side))
  -- 6. join 1, 5
  have s6a : s = (Int.gcd s w : ℤ) ^ 2 := by parley_side
  have s6b : t = (Int.gcd t w : ℤ) ^ 2 := by parley_side
  exact ⟨s6a, s6b⟩

end Parley.Stdlib.Divisibility.CoprimeSquare
