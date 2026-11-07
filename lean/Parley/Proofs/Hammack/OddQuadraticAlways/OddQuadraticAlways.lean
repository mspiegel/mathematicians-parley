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

/-! Written from proofs/hammack/odd-quadratic-always.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddQuadraticAlways.OddQuadraticAlways

theorem odd_quadratic_always (n : ℤ) :
    Odd (5 * n ^ 2 + 3 * n + 7) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : Odd (5 * n ^ 2 + 3 * n + 7) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : 5 * n ^ 2 + 3 * n + 7 = 2 * (10 * k ^ 2 + 3 * k + 3) + 1 := by
        calc 5 * n ^ 2 + 3 * n + 7 = 5 * (2 * k) ^ 2 + 3 * (2 * k) + 7 := by parley_subst s2_1
          _ = 2 * (10 * k ^ 2 + 3 * k + 3) + 1 := by parley_ring
      -- 2.3. def:odd n := 5n² + 3n + 7, from 2.2
      have s2_3 : Odd (5 * n ^ 2 + 3 * n + 7) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 3 * k + 3, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 3 * k + 3, by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 2.4. obtain k: def:odd, from C2
      obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.5. calculation
      have s2_5 : 5 * n ^ 2 + 3 * n + 7 = 2 * (10 * k ^ 2 + 13 * k + 7) + 1 := by
        calc 5 * n ^ 2 + 3 * n + 7 = 5 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 7 := by parley_subst s2_4
          _ = 2 * (10 * k ^ 2 + 13 * k + 7) + 1 := by parley_ring
      -- 2.6. def:odd n := 5n² + 3n + 7, from 2.5
      have s2_6 : Odd (5 * n ^ 2 + 3 * n + 7) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 13 * k + 7, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 5 * n ^ 2 + 3 * n + 7))).mpr ⟨10 * k ^ 2 + 13 * k + 7, by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.OddQuadraticAlways.OddQuadraticAlways
