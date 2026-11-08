module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/three-naturals-two-same-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ThreeNaturalsTwoSameParity.ThreeNaturalsTwoSameParity

set_option maxHeartbeats 400000 in
theorem three_naturals_two_same_parity (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) :
    ((Even (a - b) ∨ Even (a + c)) ∨ Even (b - c)) := by
  -- 1. mun:even-or-odd n := a − b
  have s1 : Even (a - b) ∨ Odd (a - b) := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a - b))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:or-left P := a − b is even, Q := a + c is even, from C1
    have s2_1 : Even (a - b) ∨ Even (a + c) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a - b)) (Q := Even (a + c)) hC1)
    -- 2.2. mun:or-left P := a − b is even or a + c is even, Q := b − c is even, from 2.1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a - b) ∨ Even (a + c)) (Q := Even (b - c)) s2_1)
  · skip
    -- 2.3. mun:even-or-odd n := a + c
    have s2_3 : Even (a + c) ∨ Odd (a + c) := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a + c))
    -- 2.4. cases, from 2.3
    rcases s2_3 with hC3 | hC4
    · skip
      -- 2.4.1. mun:or-right P := a − b is even, Q := a + c is even, from C3
      have s2_4_1 : Even (a - b) ∨ Even (a + c) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even (a - b)) (Q := Even (a + c)) hC3)
      -- 2.4.2. mun:or-left P := a − b is even or a + c is even, Q := b − c is even, from 2.4.1
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a - b) ∨ Even (a + c)) (Q := Even (b - c)) s2_4_1)
    · skip
      -- 2.4.3. mun:even-or-odd n := b − c
      have s2_4_3 : Even (b - c) ∨ Odd (b - c) := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b - c))
      -- 2.4.4. cases, from 2.4.3
      rcases s2_4_3 with hC5 | hC6
      · skip
        -- 2.4.4.1. mun:or-right P := a − b is even or a + c is even, Q := b − c is even, from C5
        exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even (a - b) ∨ Even (a + c)) (Q := Even (b - c)) hC5)
      · skip
        -- 2.4.4.2. obtain p: def:odd n := a − b, from C2
        obtain ⟨p, s2_4_4_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a - b))).mp hC2
        -- 2.4.4.3. obtain q: def:odd n := a + c, from C4
        obtain ⟨q, s2_4_4_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a + c))).mp hC4
        -- 2.4.4.4. obtain r: def:odd n := b − c, from C6
        obtain ⟨r, s2_4_4_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b - c))).mp hC6
        -- 2.4.4.5. algebra, from 2.4.4.2, 2.4.4.3, 2.4.4.4
        have s2_4_4_5 : 1 = 2 * (a - p - q - r - 1) := by linear_combination (norm := parley_norm) (-1) * s2_4_4_2 + (-1) * s2_4_4_3 + (-1) * s2_4_4_4
        -- 2.4.4.6. def:even n := 1, from 2.4.4.5
        have s2_4_4_6 : Even (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨a - p - q - r - 1, s2_4_4_5⟩
        -- 2.4.4.7. mun:not-both n := 1, from 2.4.4.6
        have s2_4_4_7 : ¬ Odd (1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_4_4_6)
        -- 2.4.4.8. arithmetic
        have s2_4_4_8 : Odd (1 : ℤ) := by parley_arith
        exact absurd s2_4_4_8 s2_4_4_7

end Parley.Proofs.Hammack.ThreeNaturalsTwoSameParity.ThreeNaturalsTwoSameParity
