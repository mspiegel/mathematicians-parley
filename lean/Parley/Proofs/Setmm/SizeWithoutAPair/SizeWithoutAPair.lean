module

public import NormTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Setmm.SizeOfDifference.SizeOfDifference

/-! Written from proofs/setmm/size-without-a-pair.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeWithoutAPair.SizeWithoutAPair

theorem size_without_a_pair {α : Type*} (A : Set α) (B : α) (hH2 : B ∈ A) (C : α) (hH3 : C ∈ A) (hH4 : A.Finite) (hH5 : ¬ B = C) :
    ((A \ ({B, C} : Set α)).ncard : ℤ) = (A.ncard : ℤ) - 2 := by
  -- 1. mun:pair-subset a := B, b := C, X := A, from H2, H3
  have s1 : ({B, C} : Set α) ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := A) (a := B) (b := C) hH2 hH3)
  -- 2. thm:size-of-difference B := {B, C}, from H4, 1
  have s2 : ((A \ ({B, C} : Set α)).ncard : ℤ) = (A.ncard : ℤ) - (({B, C} : Set α).ncard : ℤ) := by exact (Parley.Proofs.Setmm.SizeOfDifference.SizeOfDifference.size_of_difference (A := A) (B := ({B, C} : Set α)) hH4 s1)
  -- 3. substitute
  have s3 : ((A \ ({B, C} : Set α)).ncard : ℤ) = (A.ncard : ℤ) - 2 := by
    have c1 : (({B, C} : Set α).ncard : ℤ) = 2 := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side) | exact_mod_cast (((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side)).symm | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := B) (w := C))).mp (by parley_set_side); parley_set_side)
    have row1 : ((A \ ({B, C} : Set α)).ncard : ℤ) = (A.ncard : ℤ) - 2 := by parley_count_int; parley_subst_at c1 s2
    exact row1
  all_goals exact s3

end Parley.Proofs.Setmm.SizeWithoutAPair.SizeWithoutAPair
