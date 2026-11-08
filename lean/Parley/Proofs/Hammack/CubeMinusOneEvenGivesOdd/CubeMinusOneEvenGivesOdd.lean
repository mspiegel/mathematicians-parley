module

public import AlgebraTactics
public import SubstTactics
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cube-minus-one-even-gives-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusOneEvenGivesOdd.CubeMinusOneEvenGivesOdd

theorem cube_minus_one_even_gives_odd (x : ℤ) (hH2 : Even (x ^ 3 - 1)) :
    Odd x := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. obtain k: def:even, from C1
    obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := x))).mp hC1
    -- 2.2. calculation
    have s2_2 : x ^ 3 - 1 = 2 * (4 * k ^ 3 - 1) + 1 := by
      calc x ^ 3 - 1 = (2 * k) ^ 3 - 1 := by parley_subst s2_1
        _ = 2 * (4 * k ^ 3 - 1) + 1 := by parley_ring
    -- 2.3. def:odd n := x³ − 1, from 2.2
    have s2_3 : Odd (x ^ 3 - 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 3 - 1))).mpr ⟨4 * k ^ 3 - 1, s2_2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 3 - 1))).mpr ⟨4 * k ^ 3 - 1, s2_2⟩; parley_side)
    -- 2.4. mun:not-both n := x³ − 1, from H2
    have s2_4 : ¬ Odd (x ^ 3 - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 3 - 1) hH2)
    exact absurd s2_3 s2_4
  · skip
    exact hC2

end Parley.Proofs.Hammack.CubeMinusOneEvenGivesOdd.CubeMinusOneEvenGivesOdd
