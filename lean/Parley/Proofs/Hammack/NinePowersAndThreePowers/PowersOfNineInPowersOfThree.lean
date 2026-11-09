module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
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
        _ = 3 ^ (2 * m) := by exact (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m))
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℤ, t = 3 ^ n := ⟨2 * m, s1_2⟩
    -- 1.4. def:set-image u := t, from 1.3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:subset, from 1
  have s2 : (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ)) (Y := (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ)))).mpr s1
  -- 3. contradiction
  have s3 : ¬ (3 : ℚ) ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by
    intro hS1
    -- 3.1. obtain m: def:set-image u := 3, from S1
    obtain ⟨m, _, s3_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (9 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mp (by parley_set_side)
    -- 3.2. calculation
    have s3_2 : (3 ^ 1 : ℚ) = 3 ^ (2 * m) := by
      calc (3 ^ 1 : ℚ) = 3 := by norm_num
        _ = 9 ^ m := by parley_set_side
        _ = 3 ^ (2 * m) := by exact (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower.nine_power_is_three_power (m := m))
    -- 3.3. mun:power-cancel a := 3, m := 1, n := 2m, from 3.2
    have r238_1 : (3 : ℤ) > 1 := by parley_arith
    have s3_3 : 1 = 2 * m := ((Parley.Items.Stdlib.Numbers.mun_power_cancel (a := (3 : ℚ)) (m := (1 : ℤ)) (n := 2 * m) (by parley_set_side))).mp (by parley_set_side)
    -- 3.4. algebra, from 3.3
    have s3_4 : (m : ℚ) = 1 / 2 := by
      have s3_3_w : 1 = 2 * (m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_3; push_cast at h; linear_combination (norm := parley_norm) h
      linear_combination (norm := parley_norm) ((-1) / ((2))) * s3_3_w
    -- 3.5. inequalities
    have s3_5 : 1 / 2 ≤ (m : ℚ) := by parley_order
    -- 3.6. inequalities, from 3.5
    have s3_6 : 0 < m := by parley_order
    -- 3.7. mun:integer-step m := 0, n := m, from 3.6
    have s3_7 : 1 ≤ m := by linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := m) s3_6)]
    -- 3.8. inequalities
    have s3_8 : 2 ≤ 2 * m := by parley_order
    -- 3.9. inequalities, from 3.8
    have s3_9 : 1 < 2 * m := by parley_order
    -- 3.10. inequalities
    have s3_10 : 1 ≠ 2 * m := by parley_set_side
    exact s3_10 s3_3
  -- 4. contradiction
  have s4 : ¬ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by
    intro hS2
    -- 4.1. arithmetic
    have s4_1 : (3 : ℤ) = 3 ^ 1 := by parley_arith
    -- 4.2. exhibit, from 4.1
    have s4_2 : ∃ n : ℤ, (3 : ℚ) = 3 ^ n := ⟨(1 : ℤ), by parley_set_side⟩
    -- 4.3. def:set-image u := 3, from 4.2
    have s4_3 : (3 : ℚ) ∈ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => (3 ^ n : ℚ))) (Y := (Set.univ : Set ℤ)) (u := (3 : ℚ)) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
    -- 4.4. substitute {9^n : n ∈ ℤ} = {3^n : n ∈ ℤ} (S2) into line 4.3
    have s4_4 : (3 : ℚ) ∈ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_subst_at hS2 s4_3
    exact s3 s4_4
  -- 5. join 2, 4
  have s5 : (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) ⊆ (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) ∧ ¬ (fun n : ℤ => (9 ^ n : ℚ)) '' (Set.univ : Set ℤ) = (fun n : ℤ => (3 ^ n : ℚ)) '' (Set.univ : Set ℤ) := by parley_set_side
  exact ⟨(s5).1, (s5).2⟩

end Parley.Proofs.Hammack.NinePowersAndThreePowers.PowersOfNineInPowersOfThree
