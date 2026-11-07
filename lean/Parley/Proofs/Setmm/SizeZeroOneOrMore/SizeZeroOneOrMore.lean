module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/size-zero-one-or-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeZeroOneOrMore.SizeZeroOneOrMore

theorem size_zero_one_or_more {α : Type*} (M : Set α) (hH2 : M.Finite) :
    ((M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) ∨ ((1 : ℕ) : ℕ∞) < M.encard) := by
  -- 1. mun:card-nat0, from H2
  have s1 : 0 ≤ (M.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2); parley_set_side)
  -- 2. contradiction
  have s2 : (M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) ∨ ((1 : ℕ) : ℕ∞) < M.encard := by
    by_contra hc_hS
    have hS : ¬ ((M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) ∨ ((1 : ℕ) : ℕ∞) < M.encard) := by parley_suppose hc_hS
    -- 2.1. mun:not-either, from S
    have s2_1a : ¬ (M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).1; parley_set_side)
    have s2_1b : ¬ ((1 : ℕ) : ℕ∞) < M.encard := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞) ∨ M.encard = ((1 : ℕ) : ℕ∞)) (Q := ((1 : ℕ) : ℕ∞) < M.encard))).mp (by parley_set_side)).2; parley_set_side)
    -- 2.2. mun:not-either, from 2.1
    have s2_2a : ¬ M.encard = ((0 : ℕ) : ℕ∞) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).1; parley_set_side)
    have s2_2b : ¬ M.encard = ((1 : ℕ) : ℕ∞) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := M.encard = ((0 : ℕ) : ℕ∞)) (Q := M.encard = ((1 : ℕ) : ℕ∞)))).mp (by parley_set_side)).2; parley_set_side)
    -- 2.3. mun:nat0-nonzero m := |M|, from 1, 2.2
    have s2_3 : 0 < (M.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 2.4. inequalities, from 2.3
    have s2_4 : ((1 : ℕ) : ℕ∞) ≤ M.encard := by parley_count_int; (parley_order)
    -- 2.5. mun:le-cases x := 1, y := |M|
    have s2_5 : ((1 : ℕ) : ℕ∞) ≤ M.encard ↔ ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard := by first | exact (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))); parley_set_side)
    -- 2.6. mun:iff-from-left P := 1 ≤ |M|, Q := 1 < |M| or 1 = |M|, from 2.4, 2.5
    have s2_6 : ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := ((1 : ℕ) : ℕ∞) ≤ M.encard) (Q := ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := ((1 : ℕ) : ℕ∞) ≤ M.encard) (Q := ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := ((1 : ℕ) : ℕ∞) ≤ M.encard) (Q := ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := ((1 : ℕ) : ℕ∞) ≤ M.encard) (Q := ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := ((1 : ℕ) : ℕ∞) ≤ M.encard) (Q := ((1 : ℕ) : ℕ∞) < M.encard ∨ ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 2.7. mun:disjunctive-syllogism-left, from 2.1, 2.6
    have s2_7 : ((1 : ℕ) : ℕ∞) = M.encard := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := ((1 : ℕ) : ℕ∞) < M.encard) (Q := ((1 : ℕ) : ℕ∞) = M.encard) (by parley_set_side) (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  all_goals exact s2

end Parley.Proofs.Setmm.SizeZeroOneOrMore.SizeZeroOneOrMore
