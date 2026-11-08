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

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.EvenPlusOdd

theorem even_plus_odd (A : ℤ) (B : ℤ) (hH3 : Even A) (hH4 : Odd B) :
    Odd (A + B) := by
  -- 1. obtain k: def:even n := A, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A))).mp hH3
  -- 2. obtain l: def:odd n := B, from H4
  obtain ⟨l, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := B))).mp hH4
  -- 3. algebra, from 1, 2
  have s3 : A + B = 2 * (k + l) + 1 := by linear_combination (norm := parley_norm) s1 + s2
  -- 4. def:odd n := A + B, from 3
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := A + B))).mpr ⟨k + l, s3⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A + B))).mpr ⟨k + l, s3⟩; parley_side)

end Parley.Proofs.Setmm.Parity.EvenPlusOdd
