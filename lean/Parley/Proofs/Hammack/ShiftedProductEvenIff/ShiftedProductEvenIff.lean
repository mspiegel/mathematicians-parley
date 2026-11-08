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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/shifted-product-even-iff.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ShiftedProductEvenIff.ShiftedProductEvenIff

set_option maxHeartbeats 600000 in
theorem shifted_product_even_iff (a : ℤ) (b : ℤ) :
    (Even ((a - 3) * b ^ 2) ↔ Odd a ∨ Even b) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. mun:even-product-factor n := a − 3, from D1
    have s1 : Even (a - 3) ∨ Even (b ^ 2) := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a - 3) (b := b ^ 2))).mp hD1
    -- 2. cases, from 1
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even n := a − 3, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mp hC1
      -- 2.2. algebra, from 2.1
      have s2_2 : a = 2 * (k + 1) + 1 := by linear_combination (norm := parley_norm) s2_1
      -- 2.3. def:odd n := a, from 2.2
      have s2_3 : Odd a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mpr ⟨k + 1, s2_2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mpr ⟨k + 1, s2_2⟩; parley_side)
      -- 2.4. mun:or-left P := a is odd, Q := b is even, from 2.3
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Odd a) (Q := Even b) s2_3)
    · skip
      -- 2.5. mun:even-or-odd n := b
      have s2_5 : Even b ∨ Odd b := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))
      -- 2.6. cases, from 2.5
      have s2_6 : Even b := by
        rcases s2_5 with hC3 | hC4
        · skip
          exact hC3
        · skip
          -- 2.6.1. obtain k: def:odd n := b, from C4
          obtain ⟨k, s2_6_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp hC4
          -- 2.6.2. algebra, from 2.6.1
          have s2_6_2 : b ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by linear_combination (norm := parley_norm) (b + 2 * k + 1) * s2_6_1
          -- 2.6.3. def:odd n := b², from 2.6.2
          have s2_6_3 : Odd (b ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := b ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, s2_6_2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, s2_6_2⟩; parley_side)
          -- 2.6.4. mun:not-both n := b², from C2
          have s2_6_4 : ¬ Odd (b ^ 2) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b ^ 2) hC2)
          exact absurd s2_6_3 s2_6_4
      -- 2.7. mun:or-right P := a is odd, Q := b is even, from 2.6
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Odd a) (Q := Even b) s2_6)
  · skip
    intro hD2
    -- 3. cases, from D2
    rcases hD2 with hC5 | hC6
    · skip
      -- 3.1. obtain k: def:odd, from C5
      obtain ⟨k, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp hC5
      -- 3.2. algebra, from 3.1
      have s3_2 : a - 3 = 2 * (k - 1) := by linear_combination (norm := parley_norm) s3_1
      -- 3.3. def:even n := a − 3, from 3.2
      have s3_3 : Even (a - 3) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mpr ⟨k - 1, s3_2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a - 3))).mpr ⟨k - 1, s3_2⟩; parley_side)
      -- 3.4. mun:even-product a := a − 3, x := b², from 3.3
      exact (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a - 3) s3_3 (x := b ^ 2))
    · skip
      -- 3.5. obtain k: def:even, from C6
      obtain ⟨k, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp hC6
      -- 3.6. algebra, from 3.5
      have s3_6 : (a - 3) * b ^ 2 = 2 * (2 * (a - 3) * k ^ 2) := by linear_combination (norm := parley_norm) (a * b + 2 * a * k - 3 * b - 6 * k) * s3_5
      -- 3.7. def:even n := (a − 3)·b², from 3.6
      first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (a - 3) * b ^ 2))).mpr ⟨2 * (a - 3) * k ^ 2, s3_6⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (a - 3) * b ^ 2))).mpr ⟨2 * (a - 3) * k ^ 2, s3_6⟩; parley_side)

end Parley.Proofs.Hammack.ShiftedProductEvenIff.ShiftedProductEvenIff
