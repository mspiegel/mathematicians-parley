module

public import AlgebraTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
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
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
public import Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingInverse

set_option maxHeartbeats 400000 in
theorem alternating_inverse (f : ℤ → ℤ) (hH1 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℤ) ∧ Set.InjOn f {n : ℤ | 0 < n} ∧ Set.SurjOn f {n : ℤ | 0 < n} (Set.univ : Set ℤ)) (hH2 : ∀ n : ℤ, 0 < n → (f n : ℚ) = ((-1) ^ n.toNat * (2 * (n : ℚ) - 1) + 1) / 4) :
    (∀ m : ℤ, m > 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 2 * m) ∧ (∀ m : ℤ, m ≤ 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 1 - 2 * m) := by
  -- 1. def:one-to-one-onto, from H1
  have s1 : Set.MapsTo f {n : ℤ | 0 < n} (Set.univ : Set ℤ) ∧ Set.InjOn f {n : ℤ | 0 < n} := by first | exact (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := {n : ℤ | 0 < n}) (Y := (Set.univ : Set ℤ)) (f := f) (by parley_whole_side))).mp (by parley_set_side)).1; parley_set_side)
  -- 2. proof
  have s2 : ∀ m : ℤ, m > 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 2 * m := by
    intro m
    intro hA1
    -- 2.1. inequalities
    have s2_1 : 2 * m > 0 := by parley_order
    -- 2.2. mun:pos-int-nat m := 2·m, from 2.1
    have s2_2 : 0 < 2 * m := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 2 * m) (by parley_set_side))
    -- 2.3. def:even n := 2·m
    have s2_3 : Even (2 * m) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := 2 * m))).mpr ⟨m, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := 2 * m))).mpr ⟨m, by parley_set_side⟩; parley_set_side)
    -- 2.4. thm:alternating-value-even m := 2·m, from H2, 2.2, 2.3
    have s2_4 : (f (2 * m) : ℚ) = 2 * (m : ℚ) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3)).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven.alternating_value_even (f := f) hH2 (m := 2 * m) (by parley_set_side) s2_3); parley_set_side)
    -- 2.5. mun:inverse-value g := f, y := 2·m, from 1, 2.2
    have s2_5 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) (f (2 * m)) = 2 * m := by first | exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 2 * m) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 2 * m) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 2 * m) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 2 * m) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 2 * m) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
    -- 2.6. substitute
    have s2_6 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 2 * m := by
      have c1 : f (2 * m) = m := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s2_4
      have row1 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 2 * m := by parley_subst_at c1 s2_5
      exact row1
    all_goals parley_set_side
  -- 3. proof
  have s3 : ∀ m : ℤ, m ≤ 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 1 - 2 * m := by
    intro m
    intro hA2
    -- 3.1. inequalities
    have s3_1 : 1 - 2 * m ≥ 1 := by parley_order
    -- 3.2. inequalities, from 3.1
    have s3_2 : 1 - 2 * m > 0 := by parley_order
    -- 3.3. mun:pos-int-nat m := 1 − 2·m, from 3.2
    have s3_3 : 0 < 1 - 2 * m := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 1 - 2 * m) (by parley_set_side))
    -- 3.4. algebra
    have s3_4 : 1 - 2 * m = 2 * -m + 1 := by parley_ring
    -- 3.5. def:odd n := 1 − 2·m, from 3.4
    have s3_5 : Odd (1 - 2 * m) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := 1 - 2 * m))).mpr ⟨-m, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := 1 - 2 * m))).mpr ⟨-m, by parley_set_side⟩; parley_set_side)
    -- 3.6. thm:alternating-value-odd m := 1 − 2·m, from H2, 3.3, 3.5
    have s3_6 : (f (1 - 2 * m) : ℚ) = (1 - (1 - 2 * (m : ℚ))) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5)).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueOdd.alternating_value_odd (f := f) hH2 (m := 1 - 2 * m) (by parley_set_side) s3_5); parley_set_side)
    -- 3.7. mun:inverse-value g := f, y := 1 − 2·m, from 1, 3.3
    have s3_7 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) (f (1 - 2 * m)) = 1 - 2 * m := by first | exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 1 - 2 * m) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 1 - 2 * m) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 1 - 2 * m) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 1 - 2 * m) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℤ)) (Y := {n : ℤ | 0 < n}) (g := f) (y := 1 - 2 * m) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
    -- 3.8. substitute
    have s3_8 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 1 - 2 * m := by
      have c1 : f (1 - 2 * m) = m := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s3_6
      have row1 : (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 1 - 2 * m := by parley_subst_at c1 s3_7
      exact row1
    all_goals parley_set_side
  -- 4. join 2, 3
  have s4a : ∀ m : ℤ, m > 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 2 * m := by intro m; parley_set_side
  have s4b : ∀ m : ℤ, m ≤ 0 → (LeanBridges.Functions.inverse f {n : ℤ | 0 < n}) m = 1 - 2 * m := by intro m; parley_set_side
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingInverse
