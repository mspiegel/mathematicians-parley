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

/-! Written from proofs/hammack/binomial-even-for-odd-k.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor

theorem odd_factor (A : ℤ) (B : ℤ) (hH3 : Odd A) (hH4 : Even (A * B)) :
    Even B := by
  -- 1. obtain b: def:odd, from H3
  obtain ⟨b, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp hH3
  -- 2. obtain a: def:even n := A·B, from H4
  obtain ⟨a, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A * B))).mp hH4
  -- 3. substitute A = 2b + 1 (line 1) into line 2
  have s3 : (2 * b + 1) * B = 2 * a := by (have h := Eq.subst (motive := (fun t : ℤ => t * B = 2 * a)) s1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. algebra, from 3
  have s4 : B = 2 * (a - b * B) := by linear_combination (norm := parley_norm) s3
  -- 5. def:even n := B, from 4
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := B))).mpr ⟨a - b * B, s4⟩

end Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor
