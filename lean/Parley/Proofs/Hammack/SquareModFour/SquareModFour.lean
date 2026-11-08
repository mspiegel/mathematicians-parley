module

public import NormTactics
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/square-mod-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareModFour.SquareModFour

theorem square_mod_four (n : ℤ) :
    ((4 : ℤ) ∣ n ^ 2 ∨ (4 : ℤ) ∣ n ^ 2 - 1) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. obtain k: def:even, from C1
    obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp hC1
    -- 2.2. algebra, from 2.1
    have s2_2 : n ^ 2 = 4 * k ^ 2 := by linear_combination (norm := parley_norm) (2 * k + n) * s2_1
    -- 2.3. def:divides d := 4, n := n², from 2.2
    have s2_3 : (4 : ℤ) ∣ n ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2))).mpr ⟨k ^ 2, s2_2⟩
    -- 2.4. mun:or-left, from 2.3
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) s2_3)
  · skip
    -- 2.5. obtain k: def:odd, from C2
    obtain ⟨k, s2_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hC2
    -- 2.6. algebra, from 2.5
    have s2_6 : n ^ 2 - 1 = 4 * (k ^ 2 + k) := by linear_combination (norm := parley_norm) (2 * k + n + 1) * s2_5
    -- 2.7. def:divides d := 4, n := n² − 1, from 2.6
    have s2_7 : (4 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨k ^ 2 + k, s2_6⟩
    -- 2.8. mun:or-right, from 2.7
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (4 : ℤ) ∣ n ^ 2) (Q := (4 : ℤ) ∣ n ^ 2 - 1) s2_7)

end Parley.Proofs.Hammack.SquareModFour.SquareModFour
