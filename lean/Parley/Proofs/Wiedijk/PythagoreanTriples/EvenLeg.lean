module

public import AlgebraTactics
public import NormTactics
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg

set_option maxHeartbeats 400000 in
theorem even_leg (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) :
    (Even a ∨ Even b) := by
  -- 1. mun:even-or-odd n := a
  have s1 : Even a ∨ Odd a := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:or-left, from C1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1)
  · skip
    -- 2.2. contradiction
    have s2_2 : ¬ Odd b := by
      intro hS
      -- 2.2.1. obtain p: def:odd n := a, from C2
      obtain ⟨p, s2_2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp hC2
      -- 2.2.2. obtain q: def:odd n := b, from S
      obtain ⟨q, s2_2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp hS
      -- 2.2.3. substitute
      have s2_2_3 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by
        have c1 : a = 2 * p + 1 := by parley_subst s2_2_1
        have row1 : (2 * p + 1) ^ 2 + b ^ 2 = c ^ 2 := by parley_subst_at c1 hH4
        have c2 : b = 2 * q + 1 := by parley_subst s2_2_2
        have row2 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by parley_subst_at c2 row1
        exact row2
      -- 2.2.4. calculation
      have s2_2_4 : c ^ 2 = 2 * (2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1) := by
        calc c ^ 2 = (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 := by parley_side
          _ = 2 * (2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1) := by parley_ring
      -- 2.2.5. def:even n := c², from 2.2.4
      have s2_2_5 : Even (c ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := c ^ 2))).mpr ⟨2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1, s2_2_4⟩
      -- 2.2.6. thm:even-square n := c, from 2.2.5
      have s2_2_6 : Even c := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) (by parley_side))
      -- 2.2.7. obtain r: def:even n := c, from 2.2.6
      obtain ⟨r, s2_2_7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := c))).mp s2_2_6
      -- 2.2.8. substitute c = 2r (line 2.2.7) into line 2.2.3
      have s2_2_8 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = (2 * r) ^ 2 := by parley_subst_at s2_2_7 s2_2_3
      -- 2.2.9. algebra, from 2.2.8
      have s2_2_9 : 2 = 4 * (r ^ 2 - p ^ 2 - p - q ^ 2 - q) := by linear_combination (norm := parley_norm) s2_2_8
      -- 2.2.10. def:divides d := 4, n := 2, from 2.2.9
      have s2_2_10 : (4 : ℤ) ∣ (2 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (2 : ℤ)))).mpr ⟨r ^ 2 - p ^ 2 - p - q ^ 2 - q, s2_2_9⟩
      exact absurd s2_2_10 (by norm_num)
    -- 2.3. mun:even-or-odd n := b
    have s2_3 : Even b ∨ Odd b := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))
    -- 2.4. mun:disjunctive-syllogism P := b is even, Q := b is odd, from 2.2, 2.3
    have s2_4 : Even b := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2)
    -- 2.5. mun:or-right, from 2.4
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4)

end Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg
