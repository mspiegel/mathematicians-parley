module

public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged

theorem prefix_unchanged (T : Set ℤ) (i : ℤ) (p : ℤ) (hH4 : i < p) :
    (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∧ (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by
  -- 1. contradiction
  have s1 : ¬ p ∈ Finset.Icc (1 : ℤ) i := by
    by_contra hc_hS1
    have hS1 : p ∈ Finset.Icc (1 : ℤ) i := by parley_suppose hc_hS1
    -- 1.1. mun:range-bounds a := 1, b := i, k := p, from S1
    have s1_1 : p ≤ i := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := p) hS1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := p) hS1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := p) hS1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := p) hS1); parley_set_side)
    -- 1.2. inequalities, from H4
    have s1_2 : ¬ p ≤ i := by parley_set_side
    all_goals parley_set_side
  -- 2. mun:singleton-outside a := p, Y := {1, …, i}, from 1
  have s2 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ ({p} : Set ℤ) = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side)); parley_set_side)
  -- 3. calculation
  have s3 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by
    calc (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∪ (Set.Icc (1 : ℤ) i : Set ℤ) ∩ ({p} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))); parley_set_side)
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∪ ∅ := by parley_subst s2
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by first | exact (Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T)) | exact ((Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T)); parley_set_side)
  -- 4. mun:difference-subset X := {1, …, i}, Y := T
  have s4 : (Set.Icc (1 : ℤ) i : Set ℤ) \ T ⊆ (Set.Icc (1 : ℤ) i : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T)); parley_set_side)
  -- 5. mun:not-in-subset a := p, Y := {1, …, i} ∖ T, Z := {1, …, i}, from 1, 4
  have s5 : ¬ p ∈ (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 6. calculation
  have s6 : (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by
    calc (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = ((Set.Icc (1 : ℤ) i : Set ℤ) \ T) \ ({p} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ))); parley_set_side)
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5) | exact ((Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5); parley_set_side)
  -- 7. join 3, 6
  have s7a : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by parley_set_side
  have s7b : (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by parley_set_side
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged
