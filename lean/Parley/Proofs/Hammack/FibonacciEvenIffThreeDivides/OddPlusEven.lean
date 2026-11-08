module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/fibonacci-even-iff-three-divides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven

theorem odd_plus_even (A : ℤ) (B : ℤ) (hH3 : Odd A) (hH4 : Even B) :
    Odd (A + B) := by
  -- 1. obtain k: def:odd n := A, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp hH3
  -- 2. obtain l: def:even n := B, from H4
  obtain ⟨l, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := B))).mp hH4
  -- 3. algebra, from 1, 2
  have s3 : A + B = 2 * (k + l) + 1 := by linear_combination (norm := parley_norm) s1 + s2
  -- 4. def:odd n := A + B, from 3
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := A + B))).mpr ⟨k + l, s3⟩

end Parley.Proofs.Hammack.FibonacciEvenIffThreeDivides.OddPlusEven
