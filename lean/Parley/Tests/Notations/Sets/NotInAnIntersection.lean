module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.NotInAnIntersection

theorem not_in_an_intersection :
    ¬ (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∩ ({(3 : ℤ)} : Set ℤ) := by
  -- 1. arithmetic
  have s1 : (3 : ℤ) ≠ 1 := by parley_arith
  -- 2. arithmetic
  have s2 : (3 : ℤ) ≠ 2 := by parley_arith
  -- 3. contradiction
  have s3 : ¬ (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by
    by_contra hc_hS
    have hS : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by parley_suppose hc_hS
    -- 3.1. def:pair x := 3, u := 1, w := 2, from S
    have s3_1 : (3 : ℤ) = 1 ∨ (3 : ℤ) = 2 := by first | exact ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp (by parley_set_side); parley_set_side)
    -- 3.2. mun:disjunctive-syllogism, from 2, 3.1
    have s3_2 : (3 : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2); parley_set_side)
    all_goals parley_set_side
  -- 4. contradiction
  have s4 : ¬ (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∩ ({(3 : ℤ)} : Set ℤ) := by
    by_contra hc_hS
    have hS : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∩ ({(3 : ℤ)} : Set ℤ) := by parley_suppose hc_hS
    -- 4.1. def:intersection, from S
    have s4_1 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp (by parley_set_side)).1; parley_set_side)
    all_goals parley_set_side
  all_goals exact s4

end Parley.Tests.Notations.Sets.NotInAnIntersection
