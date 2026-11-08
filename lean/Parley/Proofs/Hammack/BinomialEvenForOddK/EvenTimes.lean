module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/binomial-even-for-odd-k.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes

theorem even_times (A : ℤ) (B : ℤ) (hH3 : Even A) :
    Even (A * B) := by
  -- 1. obtain a: def:even, from H3
  obtain ⟨a, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A))).mp hH3
  -- 2. algebra, from 1
  have s2 : A * B = 2 * (a * B) := by linear_combination (norm := parley_norm) (B) * s1
  -- 3. def:even n := A·B, from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := A * B))).mpr ⟨a * B, s2⟩

end Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes
