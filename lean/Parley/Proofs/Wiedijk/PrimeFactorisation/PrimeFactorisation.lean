module

public import AlgebraTactics
public import Functions
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Set
public import Parley.Items.Proofs.Wiedijk.PrimeFactorisation
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct

/-! Written from proofs/wiedijk/prime-factorisation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeFactorisation

set_option maxHeartbeats 800000 in
theorem prime_factorisation (n : ℤ) (hH1 : 0 < n) (hH2 : n ≥ 2) :
    (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (n = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) := by
  -- 1. induction on N starting at 1
  have s1 : ∀ N : ℤ, 0 < N → (∀ m : ℤ, m ∈ Finset.Icc 2 N → (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))))) := by
    intro N h_N
    replace h_N : 1 ≤ N := by omega
    induction N, h_N using LeanBridges.Functions.le_induction with
    | base =>
      intro m hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 1.1. mun:range-bounds a := 2, b := 1, k := m, from K1
      have s1_1 : 2 ≤ m := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (1 : ℤ)) (k := m) hK1)
      -- 1.2. mun:range-bounds a := 2, b := 1, k := m, from K1
      have s1_2 : m ≤ 1 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (1 : ℤ)) (k := m) hK1)
      -- 1.3. inequalities, from 1.1
      have s1_3 : ¬ m ≤ 1 := by parley_set_side
      exact absurd s1_2 s1_3
    | succ N hK2 hIH =>
      intro m hK3
      try push_cast at hK3
      try have hK3_bounds := Finset.mem_Icc.mp hK3
      -- 1.4. mun:range-bounds a := 2, b := N + 1, k := m, from K3
      have s1_4 : m ≤ N + 1 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := N + 1) (k := m) hK3)
      -- 1.5. mun:range-bounds a := 2, b := N + 1, k := m, from K3
      have s1_5 : 2 ≤ m := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := N + 1) (k := m) hK3)
      -- 1.6. mun:pos-int-nat
      have r199_1 : 0 < m := by parley_order
      have s1_6 : 0 < m := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := m) r199_1)
      -- 1.7. obtain p: thm:prime-factor, from 1.6
      have r203_1 : m > 1 := by parley_order
      obtain ⟨p, s1_7a, ⟨s1_7b, s1_7c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := m) (by parley_set_side) r203_1)
      have hD2_kind : ∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℚ) = (m : ℚ) / (p : ℚ) := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_quotient (n := m) (by parley_set_side) (d := p) (by parley_set_side))).mp s1_7c
      obtain ⟨r, hD2_pos, hD2⟩ := hD2_kind
      -- 1.8. def:prime, from 1.7
      have s1_8 : p > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_set_side))).mp s1_7b).1
      -- 1.9. algebra, from D2
      have s1_9 : m = p * r := by qify at *; linear_combination (norm := parley_field) (-(p : ℚ)) * hD2
      -- 1.10. inequalities, from 1.8
      have s1_10 : p - 1 > 0 := by parley_order
      -- 1.11. mun:product-positive x := p − 1, y := r, from D2, 1.10
      have s1_11 : (p - 1) * r > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := (p : ℚ) - 1) (y := (r : ℚ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (p : ℚ) - 1) (y := (r : ℚ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (p : ℚ) - 1) (y := (r : ℚ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (p : ℚ) - 1) (y := (r : ℚ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 1.12. substitute
      have s1_12 : m - r > 0 := by
        have c1 : (p - 1) * r = m - r := by linear_combination (norm := parley_norm) (-1) * s1_9
        have row1 : m - r > 0 := by parley_subst_at c1 s1_11
        exact row1
      -- 1.13. inequalities
      have s1_13 : r < m := by parley_order
      -- 1.14. transitivity, from 1.13, 1.4
      have s1_14 : r < N + 1 := by parley_order
      -- 1.15. mun:integer-step m := r, n := N + 1, from 1.14
      have s1_15 : r + 1 ≤ N + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := r) (n := N + 1) s1_14)
      -- 1.16. inequalities
      have s1_16 : r ≤ N := by parley_order
      -- 1.17. mun:le-cases x := 1, y := r, from D2
      have s1_17 : 1 < r ∨ 1 = r := by exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℚ)) (y := (r : ℚ)))).mp (by parley_set_side)
      -- 1.18. cases, from 1.17
      rcases s1_17 with hC1 | hC2
      · skip
        -- 1.18.1. mun:integer-step m := 1, n := r, from C1
        have s1_18_1 : 1 + 1 ≤ r := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := r) hC1)
        -- 1.18.2. def:range-between k := r, a := 2, b := N, from 1.16
        have r258_1 : 2 ≤ r := by parley_order
        have s1_18_2 : r ∈ Finset.Icc (2 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := r) (a := (2 : ℤ)) (b := N))).mpr (by parley_set_side)
        -- 1.18.3. instantiate m := r in IH, from 1.18.2
        have s1_18_3 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))) := by exact (hIH r (by parley_set_side))
        -- 1.18.4. thm:prime-times-product, from D2, 1.7, 1.18.3
        have s1_18_4 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (p * r = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))) := by exact (Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeTimesProduct.prime_times_product (p := p) (by parley_set_side) s1_7b (r := r) (by parley_set_side) (by parley_set_side))
        -- 1.18.5. substitute m = p·r (line 1.9) into line 1.18.4
        parley_subst_at s1_9 s1_18_4
      · skip
        set e : ℤ → ℤ := fun i : ℤ => p with hD3
        -- 1.18.6. proof
        have s1_18_6 : ∀ i : ℤ, i ∈ Finset.Icc 1 1 → Nat.Prime (e i).toNat := by
          intro i hK4
          try push_cast at hK4
          try have hK4_bounds := Finset.mem_Icc.mp hK4
          -- 1.18.6.1. D3, from K4
          have s1_18_6_1 : e i = p := by simp (disch := omega) only [hD3]
          -- 1.18.6.2. substitute e(i) = p (line 1.18.6.1) into line 1.7
          (have h := Eq.subst (motive := (fun t : ℤ => Nat.Prime t.toNat)) (s1_18_6_1).symm s1_7b; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 1.18.7. membership, from D3
        have s1_18_7 : ∀ i : ℤ, i ∈ Finset.Icc 1 1 → 0 < e i := by intro i h_i; parley_set_side
        -- 1.18.8. mun:function-into, from 1.18.7
        have s1_18_8 : Set.MapsTo e (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := e) (X := (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))
        -- 1.18.9. D3
        have r295_1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) (1 : ℤ) := by parley_set_side
        have s1_18_9 : e 1 = p := by simp (disch := omega) only [hD3]
        -- 1.18.10. substitute r = 1 (C2) into line 1.9
        have s1_18_10 : m = p := by parley_subst_at hC2 s1_9
        -- 1.18.11. calculation
        have s1_18_11 : m = (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) := by
          calc m = p := by exact s1_18_10
            _ = e 1 := by exact s1_18_9
            _ = (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ))).symm
        -- 1.18.12. exhibit, from 1.18.6, 1.18.8, 1.18.11
        have s1_18_12 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat))) := ⟨(1 : ℤ), by parley_set_side, e, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
        -- 1.18.13. D1, from 1.18.12
        parley_set_side
  -- 2. instantiate N := n in line 1
  have s2 : ∀ m : ℤ, m ∈ Finset.Icc 2 n → (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (m = (∏ i ∈ Finset.Icc (1 : ℤ) k, (f i : ℤ)) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → Nat.Prime (f i).toNat)))) := by intro m h_m; exact (s1 n (by parley_set_side) m (by parley_set_side))
  -- 3. def:range-between k := n, a := 2, b := n, from H2
  have r317_1 : n ≤ n := by parley_order
  have s3 : n ∈ Finset.Icc (2 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range_between (k := n) (a := (2 : ℤ)) (b := n))).mpr (by parley_set_side)
  -- 4. instantiate m := n in line 2, from 3
  exact (s2 n (by parley_set_side))

end Parley.Proofs.Wiedijk.PrimeFactorisation.PrimeFactorisation
