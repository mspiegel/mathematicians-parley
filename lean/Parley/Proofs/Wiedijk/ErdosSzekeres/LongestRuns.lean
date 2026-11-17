module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.ErdosSzekeres
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.ErdosSzekeres.ExtendRun

/-! Written from proofs/wiedijk/erdos-szekeres.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.ErdosSzekeres.LongestRuns

theorem longest_runs (N : ℤ) (hH1 : 0 < N) (r : ℤ) (hH2 : 0 < r) (c : ℤ → ℝ) (hH4 : ¬ (∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → c i < c j))) :
    (∃ L : ℤ → ℤ, Set.MapsTo L (Set.Icc (1 : ℤ) N : Set ℤ) (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → i < j ∧ c i < c j → L i < L j))) := by
  set U : ℤ → Set (Set ℤ) := fun k : ℤ => {S ∈ 𝒫 (Set.Icc (1 : ℤ) k : Set ℤ) | k ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q)} with hD3
  set I : ℤ → Set ℤ := fun k : ℤ => (fun S : Set ℤ => (S.ncard : ℤ)) '' (U k) with hD4
  set L : ℤ → ℤ := fun k : ℤ => sSup (I k) with hD5
  -- 1. proof
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 1 N → ((L k ∈ I k ∧ (∀ s ∈ I k, s ≤ L k)) ∧ True) ∧ L k ∈ Finset.Icc (1 : ℤ) (r - 1) := by
    intro k hK1
    have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 1.1. mun:range-bounds a := 1, b := N, from K1
    have s1_1a : 1 ≤ k := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := N) (k := k) hK1)
    have s1_1b : k ≤ N := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := N) (k := k) hK1)
    -- 1.2. def:range-between a := 1, b := k, from 1.1
    have r223_1 : k ≤ k := by linarith
    have s1_2 : k ∈ Finset.Icc (1 : ℤ) k := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (1 : ℤ)) (b := k))).mpr ⟨s1_1a, r223_1⟩
    -- 1.3. mun:singleton-subset, from 1.2
    have s1_3 : ({k} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) k : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := (Set.Icc (1 : ℤ) k : Set ℤ)) (a := k) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2))
    -- 1.4. def:singleton x := k, a := k
    have s1_4 : k ∈ ({k} : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_singleton (a := k) (x := k))).mpr rfl
    -- 1.5. proof
    have s1_5 : ∀ p ∈ ({k} : Set ℤ), ∀ q ∈ ({k} : Set ℤ), p < q → c p < c q := by
      intro p hK2
      intro q hK3
      intro hK4
      -- 1.5.1. def:singleton x := p, a := k, from K2
      have s1_5_1 : p = k := by exact ((Parley.Items.Stdlib.Sets.def_singleton (a := k) (x := p))).mp hK2
      -- 1.5.2. substitute p = k (line 1.5.1) into K4
      have s1_5_2 : k < q := Eq.subst (motive := (fun t : ℤ => t < q)) s1_5_1 hK4
      -- 1.5.3. substitute
      have s1_5_3 : k < k := by
        have c1 : q = k := by exact ((Parley.Items.Stdlib.Sets.def_singleton (a := k) (x := q))).mp hK3
        have row1 : k < k := Eq.subst (motive := (fun t : ℤ => k < t)) c1 s1_5_2
        exact row1
      -- 1.5.4. inequalities
      have s1_5_4 : ¬ k < k := by linarith
      exact absurd s1_5_3 s1_5_4
    -- 1.6. join 1.4, 1.5
    have s1_6 : k ∈ ({k} : Set ℤ) ∧ (∀ p ∈ ({k} : Set ℤ), ∀ q ∈ ({k} : Set ℤ), p < q → c p < c q) := ⟨s1_4, s1_5⟩
    -- 1.7. def:part-builder u := {k}, from D3, K1, 1.3, 1.6
    have s1_7 : ({k} : Set ℤ) ∈ U k := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => k ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) k : Set ℤ)) (u := ({k} : Set ℤ)))).mpr ⟨s1_3, s1_6.1, s1_6.2⟩
    -- 1.8. exhibit, from 1.7
    have s1_8 : ∃ S ∈ U k, (({k} : Set ℤ).ncard : ℤ) = (S.ncard : ℤ) := ⟨({k} : Set ℤ), s1_7, rfl⟩
    -- 1.9. def:set-image u := |{k}|, from D4, K1, 1.8
    have s1_9 : (({k} : Set ℤ).ncard : ℤ) ∈ I k := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun S : Set ℤ => (S.ncard : ℤ))) (Y := U k) (u := (({k} : Set ℤ).ncard : ℤ)) (Z := Set.univ) (Set.mapsTo_univ _ _))).mpr s1_8
    -- 1.10. proof
    have s1_10 : ∀ u ∈ I k, True ∧ u ≤ r - 1 := by
      intro u hK5
      -- 1.10.1. obtain T: def:set-image, from D4, K1, K5
      obtain ⟨T, s1_10_1a, s1_10_1b⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun S : Set ℤ => (S.ncard : ℤ))) (Y := U k) (u := u) (Z := Set.univ) (Set.mapsTo_univ _ _))).mp hK5
      -- 1.10.2. def:part-builder u := T, from D3, K1, 1.10.1
      have s1_10_2a : T ⊆ (Set.Icc (1 : ℤ) k : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => k ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) k : Set ℤ)) (u := T))).mp s1_10_1a).1
      have s1_10_2b : ∀ p ∈ T, ∀ q ∈ T, p < q → c p < c q := ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => k ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) k : Set ℤ)) (u := T))).mp s1_10_1a).2).2
      -- 1.10.3. mun:range-finite a := 1, b := k
      have s1_10_3 : (Set.Icc (1 : ℤ) k : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := k))
      -- 1.10.4. mun:finite-part, from 1.10.2, 1.10.3
      have s1_10_4 : T.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.Icc (1 : ℤ) k : Set ℤ)) (Y := T) s1_10_3 s1_10_2a)
      -- 1.10.5. mun:card-nat0, from 1.10.4
      have s1_10_5 : 0 ≤ (T.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := T) s1_10_4)
      -- 1.10.6. mun:range-within, from 1.1
      have s1_10_6 : (Set.Icc (1 : ℤ) k : Set ℤ) ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := N) s1_1b)
      -- 1.10.7. mun:subset-transitive, from 1.10.2, 1.10.6
      have s1_10_7 : T ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := T) (Y := (Set.Icc (1 : ℤ) k : Set ℤ)) (Z := (Set.Icc (1 : ℤ) N : Set ℤ)) s1_10_2a s1_10_6)
      -- 1.10.8. contradiction
      have s1_10_8 : ¬ r ≤ (T.ncard : ℤ) := by
        intro hS1
        -- 1.10.8.1. D1, from S1, 1.10.2
        have s1_10_8_1 : r ≤ (T.ncard : ℤ) ∧ (∀ i ∈ T, ∀ j ∈ T, i < j → c i < c j) := ⟨hS1, s1_10_2b⟩
        -- 1.10.8.2. exhibit, from 1.10.7, 1.10.8.1
        have s1_10_8_2 : ∃ S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → c i < c j) := ⟨T, s1_10_7, s1_10_8_1⟩
        exact hH4 s1_10_8_2
      -- 1.10.9. inequalities, from 1.10.5, 1.10.8
      have s1_10_9 : (T.ncard : ℤ) < r := by linarith only [s1_10_8]
      -- 1.10.10. mun:integer-step m := |T|, n := r, from 1.10.5, 1.10.9
      have s1_10_10 : (T.ncard : ℤ) + 1 ≤ r := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (T.ncard : ℤ)) (n := r) s1_10_9)
      -- 1.10.11. inequalities, from 1.10.5, 1.10.10
      have s1_10_11 : (T.ncard : ℤ) ≤ r - 1 := by linarith only [s1_10_10]
      -- 1.10.12. substitute u = |T| (line 1.10.1) into line 1.10.5
      have s1_10_12 : 0 ≤ u := Eq.subst (motive := (fun t : ℤ => 0 ≤ t)) s1_10_1b.symm s1_10_5
      -- 1.10.13. membership, from 1.10.12
      -- 1.10.14. substitute u = |T| (line 1.10.1) into line 1.10.11
      have s1_10_14 : u ≤ r - 1 := Eq.subst (motive := (fun t : ℤ => t ≤ r - 1)) s1_10_1b.symm s1_10_11
      -- 1.10.15. join 1.10.13, 1.10.14
      have s1_10_15 : True ∧ u ≤ r - 1 := ⟨trivial, s1_10_14⟩
      exact ⟨trivial, (s1_10_15).2⟩
    -- 1.11. proof
    have s1_11 : ∀ u ∈ I k, True := by
      intro u hK6
      -- 1.11.1. restate 1.10
      exact trivial
    -- 1.12. proof
    have s1_12 : ∀ u ∈ I k, u ≤ r - 1 := by
      intro u hK7
      -- 1.12.1. restate 1.10
      exact (s1_10 u hK7).2
    -- 1.13. def:subset, from 1.11
    have s1_13 : I k ⊆ (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_subset (X := I k) (Y := (Set.univ : Set ℤ)))).mpr (by intro t _; exact Set.mem_univ _)
    -- 1.14. def:upper-bound, from 1.12
    have s1_14 : ∀ s ∈ I k, s ≤ r - 1 := s1_12
    -- 1.15. exhibit, from 1.14
    have s1_15 : ∃ u : ℤ, ∀ s ∈ I k, s ≤ u := ⟨r - 1, s1_14⟩
    -- 1.16. exhibit, from 1.9
    have s1_16 : ∃ s ∈ I k, True := ⟨(({k} : Set ℤ).ncard : ℤ), s1_9, trivial⟩
    -- 1.17. mun:integer-sup-member, from D5, K1, 1.13, 1.15, 1.16
    have s1_17 : L k ∈ I k := by
      simp only [hD5] at ⊢
      exact (Parley.Items.Stdlib.Calculus.mun_integer_sup_member (S := I k) s1_13 s1_16 s1_15)
    -- 1.18. mun:integer-sup-above, from D5, K1, 1.13, 1.15
    have s1_18 : ∀ x ∈ I k, x ≤ L k := by
      intro x h_x
      simp only [hD5] at ⊢
      exact (Parley.Items.Stdlib.Calculus.mun_integer_sup_above (S := I k) (x := x) s1_13 s1_15 h_x)
    -- 1.19. def:upper-bound, from 1.18
    have s1_19 : ∀ s ∈ I k, s ≤ L k := s1_18
    -- 1.20. instantiate x := |{k}| in line 1.18, from 1.9
    have s1_20 : (({k} : Set ℤ).ncard : ℤ) ≤ L k := by exact (s1_18 (({k} : Set ℤ).ncard : ℤ) s1_9)
    -- 1.21. substitute
    have s1_21 : 1 ≤ L k := by
      have c1 : (({k} : Set ℤ).ncard : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := k))
      have row1 : 1 ≤ L k := by
        have e_nat : ({k} : Set ℤ).ncard = 1 := by exact_mod_cast c1
        have e_w : (({k} : Set ℤ).ncard : ℤ) = 1 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
        exact Eq.subst (motive := (fun t : ℤ => t ≤ L k)) e_w s1_20
      exact row1
    -- 1.22. instantiate u := L(k) in line 1.10, from 1.17
    have s1_22 : L k ≤ r - 1 := by exact (s1_10 (L k) s1_17).2
    -- 1.23. def:range-between k := L(k), a := 1, b := r − 1, from 1.21, 1.22
    have s1_23 : L k ∈ Finset.Icc (1 : ℤ) (r - 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := L k) (a := (1 : ℤ)) (b := r - 1))).mpr ⟨s1_21, s1_22⟩
    -- 1.24. join 1.17, 1.19, 1.22, 1.23
    have s1_24 : ((L k ∈ I k ∧ (∀ s ∈ I k, s ≤ L k)) ∧ True) ∧ L k ∈ Finset.Icc (1 : ℤ) (r - 1) := ⟨⟨⟨s1_17, s1_19⟩, trivial⟩, s1_23⟩
    exact ⟨⟨⟨(((s1_24).1).1).1, (((s1_24).1).1).2⟩, trivial⟩, (s1_24).2⟩
  -- 2. proof
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → i < j ∧ c i < c j → L i < L j) := by
    intro i hK8
    have hK8_bounds := Finset.mem_Icc.mp hK8
    intro j hK9
    have hK9_bounds := Finset.mem_Icc.mp hK9
    intro hK10
    -- 2.1. instantiate k := i in line 1, from K8
    have s2_1a : L i ∈ I i := by exact (s1 i hK8).1.1.1
    have s2_1b : ∀ s ∈ I i, s ≤ L i := by exact (s1 i hK8).1.1.2
    have s2_1c : L i ∈ Finset.Icc (1 : ℤ) (r - 1) := by exact (s1 i hK8).2
    -- 2.2. instantiate k := j in line 1, from K9
    have s2_2a : L j ∈ I j := by exact (s1 j hK9).1.1.1
    have s2_2b : ∀ s ∈ I j, s ≤ L j := by exact (s1 j hK9).1.1.2
    have s2_2c : L j ∈ Finset.Icc (1 : ℤ) (r - 1) := by exact (s1 j hK9).2
    -- 2.3. obtain T: def:set-image u := L(i), from D4, K8, 2.1
    obtain ⟨T, s2_3a, s2_3b⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun S : Set ℤ => (S.ncard : ℤ))) (Y := U i) (u := L i) (Z := Set.univ) (Set.mapsTo_univ _ _))).mp s2_1a
    -- 2.4. def:part-builder u := T, from D3, K8, 2.3
    have s2_4a : T ⊆ (Set.Icc (1 : ℤ) i : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => i ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := T))).mp s2_3a).1
    have s2_4b : i ∈ T := ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => i ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := T))).mp s2_3a).2).1
    have s2_4c : ∀ p ∈ T, ∀ q ∈ T, p < q → c p < c q := ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => i ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := T))).mp s2_3a).2).2
    -- 2.5. contradiction
    have s2_5 : ¬ j ∈ T := by
      intro hS2
      -- 2.5.1. mun:in-subset, from S2, 2.4
      have s2_5_1 : j ∈ Finset.Icc (1 : ℤ) i := by
        have hI : j ∈ Finset.Icc (1 : ℤ) i := by (have h := ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := j) s2_4a hS2)); simp only [Finset.mem_Icc]; exact h)
        exact hI
      -- 2.5.2. mun:range-bounds a := 1, b := i, k := j, from 2.5.1
      have s2_5_2 : j ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := j) s2_5_1)
      -- 2.5.3. inequalities, from K10
      have s2_5_3 : ¬ j ≤ i := by linarith only [hK10.1]
      exact s2_5_3 s2_5_2
    -- 2.6. mun:range-finite a := 1, b := i
    have s2_6 : (Set.Icc (1 : ℤ) i : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := i))
    -- 2.7. mun:finite-part, from 2.4, 2.6
    have s2_7 : T.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) s2_6 s2_4a)
    -- 2.8. inequalities
    have s2_8 : i ≤ j := by linarith only [hK10.1]
    -- 2.9. mun:range-within, from 2.8
    have s2_9 : (Set.Icc (1 : ℤ) i : Set ℤ) ⊆ (Set.Icc (1 : ℤ) j : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := i) (n := j) s2_8)
    -- 2.10. mun:subset-transitive, from 2.4, 2.9
    have s2_10 : T ⊆ (Set.Icc (1 : ℤ) j : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := T) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (Z := (Set.Icc (1 : ℤ) j : Set ℤ)) s2_4a s2_9)
    -- 2.11. mun:range-bounds a := 1, b := N, k := j, from K9
    have s2_11a : 1 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := N) (k := j) hK9)
    have s2_11b : j ≤ N := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := N) (k := j) hK9)
    -- 2.12. def:range-between k := j, a := 1, b := j, from 2.11
    have r426_1 : j ≤ j := by linarith
    have s2_12 : j ∈ Finset.Icc (1 : ℤ) j := ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := j))).mpr ⟨s2_11a, r426_1⟩
    -- 2.13. mun:singleton-subset, from 2.12
    have s2_13 : ({j} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) j : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := (Set.Icc (1 : ℤ) j : Set ℤ)) (a := j) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s2_12))
    -- 2.14. mun:union-subset, from 2.10, 2.13
    have s2_14 : T ∪ ({j} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) j : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := T) (Y := ({j} : Set ℤ)) (Z := (Set.Icc (1 : ℤ) j : Set ℤ)) s2_10 s2_13)
    -- 2.15. mun:in-union-singleton
    have s2_15 : j ∈ T ∪ ({j} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := j))
    -- 2.16. thm:extend-run, from H3, K8, K9, K10, 2.4
    have s2_16 : ∀ p ∈ T ∪ ({j} : Set ℤ), ∀ q ∈ T ∪ ({j} : Set ℤ), p < q → c p < c q := by exact (Parley.Proofs.Wiedijk.ErdosSzekeres.ExtendRun.extend_run (N := N) hH1 (c := c) (i := i) hK8 (j := j) hK9 (T := T) s2_4a s2_4b s2_4c hK10.1 hK10.2)
    -- 2.17. join 2.15, 2.16
    have s2_17 : j ∈ T ∪ ({j} : Set ℤ) ∧ (∀ p ∈ T ∪ ({j} : Set ℤ), ∀ q ∈ T ∪ ({j} : Set ℤ), p < q → c p < c q) := ⟨s2_15, s2_16⟩
    -- 2.18. def:part-builder u := T ∪ {j}, from D3, K9, 2.14, 2.17
    have s2_18 : T ∪ ({j} : Set ℤ) ∈ U j := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => j ∈ S ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → c p < c q))) (X := (Set.Icc (1 : ℤ) j : Set ℤ)) (u := T ∪ ({j} : Set ℤ)))).mpr ⟨s2_14, s2_17.1, s2_17.2⟩
    -- 2.19. mun:card-add-one, from 2.5, 2.7
    have s2_19 : ((T ∪ ({j} : Set ℤ)).ncard : ℤ) = (T.ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_add_one (X := T) (a := j) s2_7 s2_5)
    -- 2.20. exhibit, from 2.18, 2.19
    have s2_20 : ∃ S ∈ U j, (T.ncard : ℤ) + 1 = (S.ncard : ℤ) := ⟨T ∪ ({j} : Set ℤ), s2_18, s2_19.symm⟩
    -- 2.21. def:set-image u := |T| + 1, from D4, K9, 2.20
    have s2_21 : (T.ncard : ℤ) + 1 ∈ I j := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun S : Set ℤ => (S.ncard : ℤ))) (Y := U j) (u := (T.ncard : ℤ) + 1) (Z := Set.univ) (Set.mapsTo_univ _ _))).mpr s2_20
    -- 2.22. def:upper-bound, from 2.2
    have s2_22 : ∀ s ∈ I j, s ≤ L j := s2_2b
    -- 2.23. instantiate s := |T| + 1 in line 2.22, from 2.21
    have s2_23 : (T.ncard : ℤ) + 1 ≤ L j := by exact (s2_22 ((T.ncard : ℤ) + 1) s2_21)
    -- 2.24. substitute L(i) = |T| (line 2.3) into line 2.23
    have s2_24 : L i + 1 ≤ L j := Eq.subst (motive := (fun t : ℤ => t + 1 ≤ L j)) s2_3b.symm s2_23
    -- 2.25. inequalities, from 2.1, 2.2, 2.24
    linarith only [s2_24]
  -- 3. proof
  have s3 : ∀ k : ℤ, k ∈ Finset.Icc 1 N → L k ∈ Finset.Icc (1 : ℤ) (r - 1) := by
    intro k hK11
    have hK11_bounds := Finset.mem_Icc.mp hK11
    -- 3.1. restate 1
    exact (s1 k hK11).2
  -- 4. mun:function-into, from 3
  have s4 : Set.MapsTo L (Set.Icc (1 : ℤ) N : Set ℤ) (Set.Icc (1 : ℤ) (r - 1) : Set ℤ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := L) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (r - 1) : Set ℤ)) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s3))
  -- 5. exhibit, from 2, 4
  exact ⟨L, s4, s2⟩

end Parley.Proofs.Wiedijk.ErdosSzekeres.LongestRuns
