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
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/sum-even-same-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumEvenSameParity.SumEvenSameParity

set_option maxHeartbeats 400000 in
theorem sum_even_same_parity (x : ℤ) (y : ℤ) (hH3 : Even (x + y)) :
    (Even x ∧ Even y ∨ Odd x ∧ Odd y) := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))
  -- 2. mun:even-or-odd n := y
  have s2 : Even y ∨ Odd y := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y))
  -- 3. cases, from 1
  rcases s1 with hC1 | hC4
  · skip
    -- 3.1. obtain a: def:even n := x, from C1
    obtain ⟨a, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := x))).mp hC1
    -- 3.2. cases, from 2
    rcases s2 with hC2 | hC3
    · skip
      -- 3.2.1. join C1, C2
      have s3_2_1 : Even x ∧ Even y := by parley_side
      -- 3.2.2. mun:or-left P := x is even and y is even, Q := x is odd and y is odd, from 3.2.1
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) s3_2_1)
    · skip
      -- 3.2.3. obtain b: def:odd n := y, from C3
      obtain ⟨b, s3_2_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := y))).mp hC3
      -- 3.2.4. algebra, from 3.1, 3.2.3
      have s3_2_4 : x + y = 2 * (a + b) + 1 := by linear_combination (norm := parley_norm) s3_1 + s3_2_3
      -- 3.2.5. def:odd n := x + y, from 3.2.4
      have s3_2_5 : Odd (x + y) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, s3_2_4⟩
      -- 3.2.6. mun:not-both n := x + y, from H3
      have s3_2_6 : ¬ Odd (x + y) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) hH3)
      exact absurd s3_2_5 s3_2_6
  · skip
    -- 3.3. obtain a: def:odd n := x, from C4
    obtain ⟨a, s3_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x))).mp hC4
    -- 3.4. cases, from 2
    rcases s2 with hC5 | hC6
    · skip
      -- 3.4.1. obtain b: def:even n := y, from C5
      obtain ⟨b, s3_4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := y))).mp hC5
      -- 3.4.2. algebra, from 3.3, 3.4.1
      have s3_4_2 : x + y = 2 * (a + b) + 1 := by linear_combination (norm := parley_norm) s3_3 + s3_4_1
      -- 3.4.3. def:odd n := x + y, from 3.4.2
      have s3_4_3 : Odd (x + y) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x + y))).mpr ⟨a + b, s3_4_2⟩
      -- 3.4.4. mun:not-both n := x + y, from H3
      have s3_4_4 : ¬ Odd (x + y) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x + y) hH3)
      exact absurd s3_4_3 s3_4_4
    · skip
      -- 3.4.5. join C4, C6
      have s3_4_5 : Odd x ∧ Odd y := by parley_side
      -- 3.4.6. mun:or-right P := x is even and y is even, Q := x is odd and y is odd, from 3.4.5
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x ∧ Even y) (Q := Odd x ∧ Odd y) s3_4_5)

end Parley.Proofs.Hammack.SumEvenSameParity.SumEvenSameParity
