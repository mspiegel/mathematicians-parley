module

public import InstanceTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/erdos-szekeres.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.ErdosSzekeres.ExtendRun

set_option maxHeartbeats 800000 in
theorem extend_run (N : ℤ) (hH1 : 0 < N) (c : ℤ → ℝ) (i : ℤ) (hH3 : i ∈ Finset.Icc (1 : ℤ) N) (j : ℤ) (hH4 : j ∈ Finset.Icc (1 : ℤ) N) (T : Set ℤ) (hH5 : T ⊆ (Set.Icc (1 : ℤ) i : Set ℤ)) (hH6 : i ∈ T) (hH7 : ∀ p ∈ T, ∀ q ∈ T, p < q → c p < c q) (hH8 : i < j) (hH9 : c i < c j) :
    (∀ p ∈ T ∪ ({j} : Set ℤ), ∀ q ∈ T ∪ ({j} : Set ℤ), p < q → c p < c q) := by
  -- 1. mun:range-bounds a := 1, b := N, k := i, from H3
  have s1a : 1 ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := N) (k := i) hH3)
  have s1b : i ≤ N := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := N) (k := i) hH3)
  -- 2. mun:range-within, from 1
  have s2 : (Set.Icc (1 : ℤ) i : Set ℤ) ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := i) (n := N) s1b)
  -- 3. mun:subset-transitive, from H5, 2
  have s3 : T ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := T) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (Z := (Set.Icc (1 : ℤ) N : Set ℤ)) (by parley_whole_side) (by parley_whole_side))
  -- 4. proof
  have s4 : ∀ t ∈ T, c t < c j := by
    intro t hK1
    -- 4.1. mun:in-subset, from H5, K1
    have s4_1 : t ∈ Finset.Icc (1 : ℤ) i := by
      have hI : t ∈ Finset.Icc (1 : ℤ) i := by parley_instance ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := t) (by parley_whole_side) hK1))
      exact hI
    -- 4.2. mun:in-subset, from K1, 3
    have s4_2 : t ∈ Finset.Icc (1 : ℤ) N := by
      have hI : t ∈ Finset.Icc (1 : ℤ) N := by parley_instance ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := t) (by parley_whole_side) hK1))
      exact hI
    -- 4.3. mun:range-bounds a := 1, b := i, k := t, from 4.1
    have s4_3 : t ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := t) s4_1)
    -- 4.4. mun:le-cases x := t, y := i, from 4.3
    have s4_4 : t < i ∨ t = i := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := t) (y := i))).mp s4_3
    -- 4.5. cases, from 4.4
    rcases s4_4 with hC1 | hC2
    · skip
      -- 4.5.1. instantiate p := t, q := i in H7, from C1, H6, K1
      have s4_5_1 : c t < c i := by exact (hH7 t (by parley_set_side) i (by parley_set_side) (by parley_set_side))
      -- 4.5.2. transitivity, from 4.5.1, H9
      parley_order
    · skip
      -- 4.5.3. substitute t = i (C2) into H9
      (have h := Eq.subst (motive := (fun u : ℤ => c u < c j)) hC2.symm hH9; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. proof
  intro p hK2
  intro q hK3
  intro hK4
  -- 5.1. def:union, from K3
  have s5_1 : q ∈ T ∨ q ∈ ({j} : Set ℤ) := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := T) (Z := ({j} : Set ℤ)) (u := q))).mp hK3
  -- 5.2. def:union, from K2
  have s5_2 : p ∈ T ∨ p ∈ ({j} : Set ℤ) := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := T) (Z := ({j} : Set ℤ)) (u := p))).mp hK2
  -- 5.3. cases, from 5.1
  rcases s5_1 with hC3 | hC6
  · skip
    -- 5.3.1. mun:in-subset, from C3, H5
    have s5_3_1 : q ∈ Finset.Icc (1 : ℤ) i := by
      have hI : q ∈ Finset.Icc (1 : ℤ) i := by parley_instance ((Parley.Items.Stdlib.Sets.mun_in_subset (X := T) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (u := q) (by parley_whole_side) hC3))
      exact hI
    -- 5.3.2. mun:range-bounds a := 1, b := i, k := q, from 5.3.1
    have s5_3_2 : q ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := q) s5_3_1)
    -- 5.3.3. cases, from 5.2
    rcases s5_2 with hC4 | hC5
    · skip
      -- 5.3.3.1. instantiate p := p, q := q in H7, from C3, C4, K4
      exact (hH7 p (by parley_set_side) q (by parley_set_side) (by parley_set_side))
    · skip
      -- 5.3.3.2. def:singleton x := p, a := j, from C5
      have s5_3_3_2 : p = j := by exact ((Parley.Items.Stdlib.Sets.def_singleton (a := j) (x := p))).mp hC5
      -- 5.3.3.3. substitute p = j (line 5.3.3.2) into K4
      have s5_3_3_3 : j < q := by (have h := Eq.subst (motive := (fun t : ℤ => t < q)) s5_3_3_2 hK4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 5.3.3.4. transitivity, from 5.3.3.3, 5.3.2, H8
      have s5_3_3_4 : j < j := by parley_order
      -- 5.3.3.5. inequalities
      have s5_3_3_5 : ¬ j < j := by parley_set_side
      exact absurd s5_3_3_4 s5_3_3_5
  · skip
    -- 5.3.4. def:singleton x := q, a := j, from C6
    have s5_3_4 : q = j := by exact ((Parley.Items.Stdlib.Sets.def_singleton (a := j) (x := q))).mp hC6
    -- 5.3.5. cases, from 5.2
    have s5_3_5 : c p < c j := by
      rcases s5_2 with hC7 | hC8
      · skip
        -- 5.3.5.1. instantiate t := p in line 4, from C7
        exact (s4 p (by parley_set_side))
      · skip
        -- 5.3.5.2. def:singleton x := p, a := j, from C8
        have s5_3_5_2 : p = j := by exact ((Parley.Items.Stdlib.Sets.def_singleton (a := j) (x := p))).mp hC8
        -- 5.3.5.3. substitute p = j (line 5.3.5.2) into K4
        have s5_3_5_3 : j < q := by (have h := Eq.subst (motive := (fun t : ℤ => t < q)) s5_3_5_2 hK4; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 5.3.5.4. substitute q = j (line 5.3.4) into line 5.3.5.3
        have s5_3_5_4 : j < j := by (have h := Eq.subst (motive := (fun t : ℤ => j < t)) s5_3_4 s5_3_5_3; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 5.3.5.5. inequalities
        have s5_3_5_5 : ¬ j < j := by parley_set_side
        exact absurd s5_3_5_4 s5_3_5_5
    -- 5.3.6. substitute q = j (line 5.3.4) into line 5.3.5
    (have h := Eq.subst (motive := (fun t : ℤ => c p < c t)) s5_3_4.symm s5_3_5; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Wiedijk.ErdosSzekeres.ExtendRun
