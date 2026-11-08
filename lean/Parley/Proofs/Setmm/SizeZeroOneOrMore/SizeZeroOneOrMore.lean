module

public import OrderTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/size-zero-one-or-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeZeroOneOrMore.SizeZeroOneOrMore

theorem size_zero_one_or_more {α : Type*} (M : Set α) (hH2 : M.Finite) :
    (((M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) ∨ 1 < (M.ncard : ℤ)) := by
  -- 1. mun:card-nat0, from H2
  have s1 : 0 ≤ (M.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := M) hH2)
  -- 2. contradiction
  by_contra hS
  -- 2.1. mun:not-either, from S
  have s2_1a : ¬ ((M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).1; parley_set_side)
  have s2_1b : ¬ 1 < (M.ncard : ℤ) := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0 ∨ (M.ncard : ℤ) = 1) (Q := 1 < (M.ncard : ℤ)))).mp (by parley_set_side)).2; parley_set_side)
  -- 2.2. mun:not-either, from 2.1
  have s2_2a : (M.ncard : ℤ) ≠ 0 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).1; parley_set_side)
  have s2_2b : (M.ncard : ℤ) ≠ 1 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := (M.ncard : ℤ) = 0) (Q := (M.ncard : ℤ) = 1))).mp (by parley_set_side)).2; parley_set_side)
  -- 2.3. mun:nat0-nonzero m := |M|, from 1, 2.2
  have s2_3 : 0 < (M.ncard : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side))
  -- 2.4. inequalities, from 2.3
  have s2_4 : 1 ≤ (M.ncard : ℤ) := by parley_count_int; (parley_order)
  -- 2.5. mun:le-cases x := 1, y := |M|
  have s2_5 : 1 ≤ (M.ncard : ℤ) ↔ 1 < (M.ncard : ℤ) ∨ 1 = (M.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := (M.ncard : ℤ))); parley_set_side)
  -- 2.6. mun:iff-from-left P := 1 ≤ |M|, Q := 1 < |M| or 1 = |M|, from 2.4, 2.5
  have s2_6 : 1 < (M.ncard : ℤ) ∨ 1 = (M.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := 1 ≤ (M.ncard : ℤ)) (Q := 1 < (M.ncard : ℤ) ∨ 1 = (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side))
  -- 2.7. mun:disjunctive-syllogism-left, from 2.1, 2.6
  have s2_7 : 1 = (M.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := 1 < (M.ncard : ℤ)) (Q := 1 = (M.ncard : ℤ)) (by parley_set_side) (by parley_set_side))
  exact s2_2b s2_7.symm

end Parley.Proofs.Setmm.SizeZeroOneOrMore.SizeZeroOneOrMore
