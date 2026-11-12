module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Proofs.Wiedijk.PrimeFactorisation
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/prime-factorisation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct

theorem prime_times_product (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (r : ℤ) (hH3 : 0 < r) (hH4 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) :
    (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (p * r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) := by
  -- 1. D1, from H4
  have s1 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))) := by parley_set_side
  -- 2. obtain j, g from line 1
  obtain ⟨j, s2a, g, s2b, ⟨s2c, s2d⟩⟩ := s1
  set h : ℤ → ℤ := fun i : ℤ => @ite _ (i ≤ j) (Classical.propDecidable (i ≤ j)) (g i) p with hD2
  -- 3. proof
  have s3 : ∀ i : ℤ, i ∈ Finset.Icc 1 j → h i = g i := by
    intro i hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 3.1. mun:range-bounds a := 1, b := j, k := i, from K1
    have s3_1 : i ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := j) (k := i) hK1)
    -- 3.2. D2, from 3.1
    have r49_1 : i ∈ Finset.Icc (1 : ℤ) (j + 1) := by exact (Parley.Items.Stdlib.Sums.mun_range_extended (a := (1 : ℤ)) (b := j) (k := i) hK1)
    simp (disch := omega) only [hD2, if_pos s3_1]
  -- 4. proof
  have s4 : ∀ i : ℤ, i ∈ Finset.Icc 1 (j + 1) → Nat.Prime (h i).toNat := by
    intro i hK2
    try push_cast at hK2
    try have hK2_bounds := Finset.mem_Icc.mp hK2
    -- 4.1. axi:excluded-middle P := i ≤ j
    have s4_1 : i ≤ j ∨ ¬ i ≤ j := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ j))
    -- 4.2. cases, from 4.1
    rcases s4_1 with hC1 | hC2
    · skip
      -- 4.2.1. D2, from C1, K2
      have s4_2_1 : h i = g i := by simp (disch := omega) only [hD2, if_pos hC1]
      -- 4.2.2. def:range-between k := i, a := 1, b := j, from C1
      have r69_1 : 1 ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := j + 1) (k := i) hK2)
      have s4_2_2 : i ∈ Finset.Icc (1 : ℤ) j := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := j))).mpr ⟨r69_1, hC1⟩
      -- 4.2.3. instantiate i := i in line 2, from 4.2.2
      have s4_2_3 : Nat.Prime (g i).toNat := by exact (s2d i s4_2_2)
      -- 4.2.4. substitute h(i) = g(i) (line 4.2.1) into line 4.2.3
      have r76_1 : 0 < g i := by
        have hI : 0 < g i := by parley_instance ((Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) j : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s4_2_2) (by parley_whole_side)))
        exact hI
      (have h := Eq.subst (motive := (fun t : ℤ => Nat.Prime t.toNat)) s4_2_1.symm s4_2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    · skip
      -- 4.2.5. D2, from C2, K2
      have s4_2_5 : h i = p := by simp (disch := omega) only [hD2, if_neg hC2]
      -- 4.2.6. substitute h(i) = p (line 4.2.5) into H2
      (have h := Eq.subst (motive := (fun t : ℤ => Nat.Prime t.toNat)) s4_2_5.symm hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. proof
  have s5 : ∀ i : ℤ, i ∈ Finset.Icc 1 (j + 1) → 0 < h i := by
    intro i hK3
    try push_cast at hK3
    try have hK3_bounds := Finset.mem_Icc.mp hK3
    -- 5.1. axi:excluded-middle P := i ≤ j
    have s5_1 : i ≤ j ∨ ¬ i ≤ j := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i ≤ j))
    -- 5.2. cases, from 5.1
    rcases s5_1 with hC3 | hC4
    · skip
      -- 5.2.1. D2, from C3, K3
      have s5_2_1 : h i = g i := by simp (disch := omega) only [hD2, if_pos hC3]
      -- 5.2.2. def:range-between k := i, a := 1, b := j, from C3
      have r105_1 : 1 ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := j + 1) (k := i) hK3)
      have s5_2_2 : i ∈ Finset.Icc (1 : ℤ) j := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := j))).mpr ⟨r105_1, hC3⟩
      -- 5.2.3. mun:function-value f := g, from 5.2.2
      have s5_2_3 : 0 < g i := by
        have hI : 0 < g i := by parley_instance ((Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) j : Set ℤ)) (E := {n : ℤ | 0 < n}) (f := g) (x := i) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s5_2_2) (by parley_whole_side)))
        exact hI
      -- 5.2.4. substitute h(i) = g(i) (line 5.2.1) into line 5.2.3
      (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s5_2_1.symm s5_2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    · skip
      -- 5.2.5. D2, from C4, K3
      have s5_2_5 : h i = p := by simp (disch := omega) only [hD2, if_neg hC4]
      -- 5.2.6. substitute h(i) = p (line 5.2.5) into H1
      (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) s5_2_5.symm hH1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. mun:function-into, from 5
  have s6 : Set.MapsTo h (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (1 : ℤ) (j + 1) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))
  -- 7. mun:product-termwise a := 1, b := j, t := h, u := g, from 3
  have r128_1 : Set.MapsTo h (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) {n : ℤ | 0 < n} := by exact s6
  have s7 : (∏ i ∈ Finset.Icc (1 : ℤ) j, (h i : ℤ)) = (∏ i ∈ Finset.Icc (1 : ℤ) j, (g i : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_product_termwise (t := h) (u := g) (X := (Set.univ : Set ℤ)) (Z := Set.univ) (Y := (Set.univ : Set ℤ)) (W := Set.univ) (a := (1 : ℤ)) (b := j) s3 (by parley_set_side) (by parley_set_side))
  -- 8. inequalities
  have s8 : ¬ j + 1 ≤ j := by linarith
  -- 9. def:range-between k := j + 1, a := 1, b := j + 1
  have r135_1 : 1 ≤ j + 1 := by linarith only [s2a]
  have r135_2 : j + 1 ≤ j + 1 := by linarith
  have s9 : j + 1 ∈ Finset.Icc (1 : ℤ) (j + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := j + 1) (a := (1 : ℤ)) (b := j + 1))).mpr ⟨r135_1, r135_2⟩
  -- 10. D2, from 8, 9
  have s10 : h (j + 1) = p := by simp (disch := omega) only [hD2, if_neg s8]
  -- 11. substitute r = ∏(i ∈ {1, …, j}) g(i) (line 2)
  have s11 : (∏ i ∈ Finset.Icc (1 : ℤ) j, (g i : ℤ)) * h (j + 1) = r * h (j + 1) := by (have h := congrArg (fun t : ℤ => t * h (j + 1)) s2c.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 12. calculation
  have r146_1 : j ≥ 1 := by parley_set_side
  have s12 : p * r = (∏ i ∈ Finset.Icc (1 : ℤ) (j + 1), (h i : ℤ)) := by
    calc p * r = r * p := by parley_ring
      _ = r * h (j + 1) := by (have h := congrArg (fun t : ℤ => r * t) s10.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) j, (g i : ℤ)) * h (j + 1) := by exact s11.symm
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) j, (h i : ℤ)) * h (j + 1) := by (have h := congrArg (fun t : ℤ => t * h (j + 1)) s7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) (j + 1), (h i : ℤ)) := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_extended (t := h) (a := (1 : ℤ)) (n := j) r146_1).symm
  -- 13. exhibit, from 4, 6, 12
  have s13 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (p * r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))) := ⟨j + 1, add_pos (s2a) (by norm_num), h, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
  -- 14. D1, from 13
  parley_set_side

end Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct
