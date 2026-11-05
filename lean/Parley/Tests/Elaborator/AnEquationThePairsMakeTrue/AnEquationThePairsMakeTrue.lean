module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/an-equation-the-pairs-make-true.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnEquationThePairsMakeTrue.AnEquationThePairsMakeTrue

theorem an_equation_the_pairs_make_true {α : Type*} (A : Set α) (B : Set α) (hH3 : A.Finite) (hH4 : B.Finite) (hH5 : A ∩ B = ∅) :
    (A ∪ B).encard = A.encard + B.encard := by
  -- 1. mun:card-nat0 X := A, from H3
  have s1 : 0 ≤ (A.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := A) hH3); parley_set_side)
  -- 2. mun:card-nat0 X := B, from H4
  have s2 : 0 ≤ (B.ncard : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | exact ((Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4) | (have h := (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := B) hH4); parley_set_side)
  -- 3. mun:card-disjoint-union X := A, Y := B, m := |A|, n := |B|, from H5, 1, 2
  have s3 : (A ∪ B).encard = A.encard + B.encard := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := A) (Y := B) (m := A.ncard) (n := B.ncard) (by parley_set_side) (by parley_set_side) hH5); parley_set_side)
  all_goals exact s3

end Parley.Tests.Elaborator.AnEquationThePairsMakeTrue.AnEquationThePairsMakeTrue
