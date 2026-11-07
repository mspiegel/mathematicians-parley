module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent

/-! Written from proofs/wiedijk/divisibility-by-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DivisibilityByThree.DivisibilityByThree

theorem divisibility_by_three (n : ℤ) (hH1 : 0 ≤ n) (d : ℤ → ℤ) :
    ((3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) ↔ (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ))) := by
  -- 1. proof
  have s1 : ∀ k : ℤ, 0 ≤ k → (3 : ℤ) ∣ d k * 10 ^ k.toNat - d k := by
    intro k hK
    -- 1.1. thm:ten-power-congruent
    have s1_1 : (10 ^ k.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent.ten_power_congruent (k := k) (by parley_side)); parley_side)
    -- 1.2. def:congruent-mod, from 1.1
    have s1_2 : (3 : ℤ) ∣ (10 ^ k.toNat - 1 : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (10 ^ k.toNat : ℤ)) (b := (1 : ℤ)))).mp (by parley_side); parley_side)
    -- 1.3. mun:divides-multiple e := 3, a := 10^k − 1, x := d(k), from H2, 1.2
    have s1_3 : (3 : ℤ) ∣ (10 ^ k.toNat - 1) * d k := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (3 : ℤ)) (a := (10 ^ k.toNat - 1 : ℤ)) (x := d k) s1_2); parley_side)
    -- 1.4. substitute
    have s1_4 : (3 : ℤ) ∣ d k * 10 ^ k.toNat - d k := by
      have c1 : (10 ^ k.toNat - 1) * d k = d k * 10 ^ k.toNat - d k := by parley_ring
      have row1 : (3 : ℤ) ∣ d k * 10 ^ k.toNat - d k := by parley_subst_at c1 s1_3
      exact row1
    all_goals exact s1_4
  -- 2. mun:sum-divisible m := 3, from 1
  have s2 : (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat - d k : ℤ)) := by first | exact (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_divisible (t := (fun k : ℤ => d k * 10 ^ k.toNat - d k)) (n := n) (by parley_side) (m := (3 : ℤ)) (by parley_side)); parley_side)
  -- 3. substitute
  have s3 : (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) - (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) := by
    have c1 : (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat - d k : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) - (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_difference (t := (fun k : ℤ => d k * 10 ^ k.toNat)) (u := d) (n := n) (by parley_side)); parley_side)
    have row1 : (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) - (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  have s4 : (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) ≡ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) [ZMOD (3 : ℤ)] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)))).mpr (by parley_side); parley_side)
  -- 5. mun:congruent-divides m := 3, from 4
  have s5 : (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) ↔ (3 : ℤ) ∣ (∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4) | exact ((Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_divides (m := (3 : ℤ)) (a := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k * 10 ^ k.toNat : ℤ)) (b := ∑ k ∈ Finset.Icc (0 : ℤ) n, (d k : ℤ)) s4); parley_side)
  all_goals exact s5

end Parley.Proofs.Wiedijk.DivisibilityByThree.DivisibilityByThree
