module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself

theorem an_obtain_through_an_iff_said_of_itself (a : ℤ) :
    (∃ q : ℤ, q * 3 + a % (3 : ℤ) = a) := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ a % (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)); parley_side)
  -- 2. mun:mod-less b := 3
  have s2 : a % (3 : ℤ) < 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)); parley_side)
  -- 3. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1, 2
  obtain ⟨q, s3⟩ := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := 3) (by parley_side) (r := (a % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side)]); parley_side)))).mp (by parley_side)
  -- 4. exhibit, from 3
  have s4 : ∃ q : ℤ, q * 3 + a % (3 : ℤ) = a := ⟨q, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself
