module

public import AlgebraTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
public import Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingBijection

set_option maxHeartbeats 800000 in
theorem alternating_bijection (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, 0 < n → (f n : ℚ) = ((-1) ^ n.toNat * (2 * (n : ℚ) - 1) + 1) / 4) :
    (Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℤ) ∧ Set.InjOn f {n : ℤ | 0 < n} ∧ Set.SurjOn f {n : ℤ | 0 < n} (Set.univ : Set ℤ)) := by
  -- 1. proof
  have s1 : ∀ s : ℤ, 0 < s → (∀ t : ℤ, 0 < t → f s = f t → s = t) := by
    intro s hK1
    intro t hK2
    intro hA1
    -- 1.1. mun:even-or-odd n := s
    have s1_1 : Even s ∨ Odd s := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := s))
    -- 1.2. mun:even-or-odd n := t
    have s1_2 : Even t ∨ Odd t := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := t))
    -- 1.3. cases, from 1.1
    rcases s1_1 with hC1 | hC2
    · skip
      -- 1.3.1. thm:alternating-value-even m := s, from C1, H2
      have s1_3_1 : (f s : ℚ) = (s : ℚ) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := s) (by parley_set_side) hC1)
      -- 1.3.2. cases, from 1.2
      rcases s1_2 with hC3 | hC4
      · skip
        -- 1.3.2.1. calculation
        have s1_3_2_1 : (s : ℚ) / 2 = (t : ℚ) / 2 := by
          calc (s : ℚ) / 2 = (f s : ℚ) := by parley_set_side
            _ = (f t : ℚ) := by parley_set_side
            _ = (t : ℚ) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := t) (by parley_set_side) hC3)
        -- 1.3.2.2. algebra, from 1.3.2.1
        qify at *; linear_combination (norm := parley_norm) ((8) / ((4))) * s1_3_2_1
      · skip
        -- 1.3.2.3. calculation
        have s1_3_2_3 : (s : ℚ) / 2 = (1 - (t : ℚ)) / 2 := by
          calc (s : ℚ) / 2 = (f s : ℚ) := by parley_set_side
            _ = (f t : ℚ) := by parley_set_side
            _ = (1 - (t : ℚ)) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := t) (by parley_set_side) hC4)
        -- 1.3.2.4. algebra, from 1.3.2.3
        have s1_3_2_4 : s + t = 1 := by qify at *; linear_combination (norm := parley_norm) ((8) / ((4))) * s1_3_2_3
        -- 1.3.2.5. inequalities, from K1, K2
        have s1_3_2_5 : s + t > 1 := by parley_order
        -- 1.3.2.6. inequalities
        have s1_3_2_6 : s + t ≠ 1 := by parley_set_side
        exact absurd s1_3_2_4 s1_3_2_6
    · skip
      -- 1.3.3. thm:alternating-value-odd m := s, from C2, H2
      have s1_3_3 : (f s : ℚ) = (1 - (s : ℚ)) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := s) (by parley_set_side) hC2)
      -- 1.3.4. cases, from 1.2
      rcases s1_2 with hC5 | hC6
      · skip
        -- 1.3.4.1. calculation
        have s1_3_4_1 : (1 - (s : ℚ)) / 2 = (t : ℚ) / 2 := by
          calc (1 - (s : ℚ)) / 2 = (f s : ℚ) := by parley_set_side
            _ = (f t : ℚ) := by parley_set_side
            _ = (t : ℚ) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := t) (by parley_set_side) hC5)
        -- 1.3.4.2. algebra, from 1.3.4.1
        have s1_3_4_2 : s + t = 1 := by qify at *; linear_combination (norm := parley_norm) ((-8) / ((4))) * s1_3_4_1
        -- 1.3.4.3. inequalities, from K1, K2
        have s1_3_4_3 : s + t > 1 := by parley_order
        -- 1.3.4.4. inequalities
        have s1_3_4_4 : s + t ≠ 1 := by parley_set_side
        exact absurd s1_3_4_2 s1_3_4_4
      · skip
        -- 1.3.4.5. calculation
        have s1_3_4_5 : (1 - (s : ℚ)) / 2 = (1 - (t : ℚ)) / 2 := by
          calc (1 - (s : ℚ)) / 2 = (f s : ℚ) := by parley_set_side
            _ = (f t : ℚ) := by parley_set_side
            _ = (1 - (t : ℚ)) / 2 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := t) (by parley_set_side) hC6)
        -- 1.3.4.6. algebra, from 1.3.4.5
        qify at *; linear_combination (norm := parley_norm) ((-8) / ((4))) * s1_3_4_5
  -- 2. def:one-to-one, from H1, 1
  have s2 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℤ) ∧ Set.InjOn f {n : ℤ | 0 < n} := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side)
  -- 3. proof
  have s3 : ∀ y : ℤ, ∃ x : ℤ, 0 < x ∧ y = f x := by
    intro y
    -- 3.1. mun:nonneg-or-neg x := −y
    have s3_1 : -y ≥ 0 ∨ -y < 0 := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := -y))
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC7 | hC8
    · skip
      -- 3.2.1. inequalities
      have s3_2_1 : 1 - 2 * y ≥ 1 := by parley_order
      -- 3.2.2. inequalities, from 3.2.1
      have s3_2_2 : 1 - 2 * y > 0 := by parley_order
      -- 3.2.3. mun:pos-int-nat m := 1 − 2·y, from 3.2.2
      have s3_2_3 : 0 < 1 - 2 * y := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 1 - 2 * y) s3_2_2)
      -- 3.2.4. algebra
      have s3_2_4 : 1 - 2 * y = 2 * -y + 1 := by parley_ring
      -- 3.2.5. def:odd n := 1 − 2·y, from 3.2.4
      have s3_2_5 : Odd (1 - 2 * y) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 1 - 2 * y))).mpr ⟨-y, s3_2_4⟩
      -- 3.2.6. thm:alternating-value-odd m := 1 − 2·y, from H2, 3.2.3, 3.2.5
      have s3_2_6 : (f (1 - 2 * y) : ℚ) = (1 - (1 - 2 * (y : ℚ))) / 2 := by simpa using (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * y) (by parley_set_side) s3_2_5)
      -- 3.2.7. algebra, from 3.2.6
      have s3_2_7 : y = f (1 - 2 * y) := by qify at *; linear_combination (norm := parley_norm) ((-2) / ((2))) * s3_2_6
      -- 3.2.8. exhibit, from 3.2.3, 3.2.7
      exact ⟨1 - 2 * y, s3_2_3, s3_2_7⟩
    · skip
      -- 3.2.9. inequalities
      have s3_2_9 : 2 * y > 0 := by parley_order
      -- 3.2.10. mun:pos-int-nat m := 2·y, from 3.2.9
      have s3_2_10 : 0 < 2 * y := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 2 * y) s3_2_9)
      -- 3.2.11. def:even n := 2·y
      have s3_2_11 : Even (2 * y) := ((Parley.Items.Stdlib.Divisibility.def_even (n := 2 * y))).mpr ⟨y, by parley_set_side⟩
      -- 3.2.12. thm:alternating-value-even m := 2·y, from H2, 3.2.10, 3.2.11
      have s3_2_12 : (f (2 * y) : ℚ) = 2 * (y : ℚ) / 2 := by simpa using (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * y) (by parley_set_side) s3_2_11)
      -- 3.2.13. algebra, from 3.2.12
      have s3_2_13 : y = f (2 * y) := by qify at *; linear_combination (norm := parley_norm) ((-2) / ((2))) * s3_2_12
      -- 3.2.14. exhibit, from 3.2.10, 3.2.13
      exact ⟨2 * y, s3_2_10, s3_2_13⟩
  -- 4. def:onto, from H1, 3
  have s4 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℤ) ∧ Set.SurjOn f {n : ℤ | 0 < n} (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Functions.def_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side)
  -- 5. def:one-to-one-onto, from 2, 4
  exact ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side)

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingBijection
