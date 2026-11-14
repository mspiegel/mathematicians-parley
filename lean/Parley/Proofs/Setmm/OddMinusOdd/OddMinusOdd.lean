module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/odd-minus-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddMinusOdd.OddMinusOdd

theorem odd_minus_odd (A : ℤ) (B : ℤ) (hH3 : Odd A) (hH4 : Odd B) :
    (2 : ℤ) ∣ A - B := by
  -- 1. obtain a: def:odd n := A, from H3
  obtain ⟨a, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp hH3
  -- 2. obtain b: def:odd n := B, from H4
  obtain ⟨b, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := B))).mp hH4
  -- 3. algebra, from 1, 2
  have s3 : A - B = 2 * (a - b) := by linear_combination s1 + (-1) * s2
  -- 4. def:divides d := 2, n := A − B, from 3
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := A - B))).mpr ⟨a - b, s3⟩

end Parley.Proofs.Setmm.OddMinusOdd.OddMinusOdd
