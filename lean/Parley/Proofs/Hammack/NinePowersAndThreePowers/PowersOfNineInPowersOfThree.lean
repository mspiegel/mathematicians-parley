module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.PowersOfNineInPowersOfThree

set_option maxHeartbeats 600000 in
theorem powers_of_nine_in_powers_of_three :
    ((fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) ∧ ¬ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ)) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ), t ∈ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (9 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 1.2. calculation
    have s1_2 : t = 3 ^ (2 * m) := by
      calc t = 9 ^ m := by parley_set_side
        _ = 3 ^ (2 * m) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)) | exact_mod_cast ((Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m))).symm | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); parley_set_side)
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℤ, t = 3 ^ n := ⟨2 * m, by parley_set_side⟩
    -- 1.4. def:set-image u := t, from 1.3
    have s1_4 : t ∈ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_4
  -- 2. def:subset, from 1
  have s2 : (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 3. contradiction
  have s3 : ¬ (3 : ℚ) ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by
    by_contra hc_hS1
    have hS1 : (3 : ℚ) ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_suppose hc_hS1
    -- 3.1. obtain m: def:set-image u := 3, from S1
    obtain ⟨m, _, s3_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (9 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.2. calculation
    have s3_2 : (3 ^ 1 : ℚ) = 3 ^ (2 * m) := by
      calc (3 ^ 1 : ℚ) = 3 := by norm_num
        _ = 9 ^ m := by parley_set_side
        _ = 3 ^ (2 * m) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)) | exact_mod_cast ((Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m))).symm | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m)); parley_set_side)
    -- 3.3. mun:power-cancel a := 3, m := 1, n := 2m, from 3.2
    have r238_1 : (3 : ℤ) > 1 := by parley_arith
    have s3_3 : 1 = 2 * m := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side)).symm | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 3.4. algebra, from 3.3
    have s3_4 : (m : ℚ) = 1 / 2 := by
      have s3_3_w : 1 = 2 * (m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_3; push_cast at h; linear_combination (norm := parley_norm) h
      linear_combination (norm := parley_norm) ((-1) / ((2))) * s3_3_w
    -- 3.5. inequalities
    have s3_5 : 1 / 2 ≤ (m : ℚ) := by parley_order
    -- 3.6. inequalities, from 3.5
    have s3_6 : 0 < m := by parley_order
    -- 3.7. mun:integer-step m := 0, n := m, from 3.6
    have s3_7 : 1 ≤ m := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := m) s3_6)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := m) s3_6); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := m) s3_6) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := m) s3_6); parley_set_side)
    -- 3.8. inequalities
    have s3_8 : 2 ≤ 2 * m := by parley_order
    -- 3.9. inequalities, from 3.8
    have s3_9 : 1 < 2 * m := by parley_order
    -- 3.10. inequalities
    have s3_10 : 1 ≠ 2 * m := by parley_set_side
    all_goals parley_set_side
  -- 4. contradiction
  have s4 : ¬ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by
    by_contra hc_hS2
    have hS2 : (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_suppose hc_hS2
    -- 4.1. arithmetic
    have s4_1 : (3 : ℤ) = 3 ^ 1 := by parley_arith
    -- 4.2. exhibit, from 4.1
    have s4_2 : ∃ n : ℤ, (3 : ℚ) = 3 ^ n := ⟨(1 : ℤ), by parley_set_side⟩
    -- 4.3. def:set-image u := 3, from 4.2
    have s4_3 : (3 : ℚ) ∈ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    -- 4.4. substitute {9^n : n ∈ ℤ} = {3^n : n ∈ ℤ} (S2) into line 4.3
    have s4_4 : (3 : ℚ) ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_subst_at hS2 s4_3
    all_goals parley_set_side
  -- 5. join 2, 4
  have s5 : (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) ∧ ¬ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_set_side
  all_goals exact s5

end Parley.Proofs.Hammack.NinePowersAndThreePowers.PowersOfNineInPowersOfThree
