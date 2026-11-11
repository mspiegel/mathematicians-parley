module

public import SetTactics
public import SubstTactics
public import Tactics
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
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged

theorem prefix_unchanged (T : Set ℤ) (i : ℤ) (p : ℤ) (hH4 : i < p) :
    (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∧ (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by
  -- 1. contradiction
  have s1 : ¬ p ∈ Finset.Icc (1 : ℤ) i := by
    intro hS1
    -- 1.1. mun:range-bounds a := 1, b := i, k := p, from S1
    have s1_1 : p ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := i) (k := p) hS1)
    -- 1.2. inequalities, from H4
    have s1_2 : ¬ p ≤ i := by parley_set_side
    exact s1_2 s1_1
  -- 2. mun:singleton-outside a := p, Y := {1, …, i}, from 1
  have s2 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ ({p} : Set ℤ) = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_singleton_outside (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1))
  -- 3. calculation
  have s3 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by
    calc (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∪ (Set.Icc (1 : ℤ) i : Set ℤ) ∩ ({p} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ)))
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T ∪ ∅ := by parley_subst s2
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by exact (Parley.Items.Stdlib.Sets.mun_union_empty (Y := (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T))
  -- 4. mun:difference-subset X := {1, …, i}, Y := T
  have s4 : (Set.Icc (1 : ℤ) i : Set ℤ) \ T ⊆ (Set.Icc (1 : ℤ) i : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T))
  -- 5. mun:not-in-subset a := p, Y := {1, …, i} ∖ T, Z := {1, …, i}, from 1, 4
  have s5 : ¬ p ∈ (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (Z := (Set.Icc (1 : ℤ) i : Set ℤ)) (a := p) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1) s4)
  -- 6. calculation
  have s6 : (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by
    calc (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = ((Set.Icc (1 : ℤ) i : Set ℤ) \ T) \ ({p} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_by_union (X := (Set.Icc (1 : ℤ) i : Set ℤ)) (Y := T) (Z := ({p} : Set ℤ)))
      _ = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by exact (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := (Set.Icc (1 : ℤ) i : Set ℤ) \ T) (a := p) s5)
  -- 7. join 3, 6
  have s7a : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by parley_set_side
  have s7b : (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({p} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by parley_set_side
  exact ⟨s7a, s7b⟩

end Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged
