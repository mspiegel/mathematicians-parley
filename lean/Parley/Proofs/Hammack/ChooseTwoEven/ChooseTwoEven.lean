module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library
public import Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula

/-! Written from proofs/hammack/choose-two-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoEven

theorem choose_two_even (a : ℕ) (hH2 : (a : ℤ) ≡ (0 : ℤ) [ZMOD (4 : ℤ)] ∨ (a : ℤ) ≡ (1 : ℤ) [ZMOD (4 : ℤ)]) :
    Even (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) := by
  -- 1. thm:choose-two-formula n := a
  have s1 : (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℚ) = (a : ℚ) * ((a : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a)) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a)) | exact_mod_cast ((Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a))).symm | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a)); qify; linear_combination (norm := parley_norm) h)
  -- 2. cases, from H2
  have s2 : Even (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) := by
    rcases hH2 with hC1 | hC2
    · skip
      -- 2.1. def:congruent-mod, from C1
      have s2_1 : (4 : ℤ) ∣ (a : ℤ) := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (0 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (0 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (0 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (0 : ℤ)))).mp (by parley_side)
      -- 2.2. obtain k: def:divides d := 4, n := a, from 2.1
      obtain ⟨k, s2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (a : ℤ)))).mp (by parley_side)
      -- 2.3. algebra, from 1, 2.2
      have s2_3 : (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) = 2 * (k * (4 * k - 1)) := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s1 + ((1 / 2 : ℚ) * (a : ℚ) + 2 * (k : ℚ) - (1 / 2 : ℚ)) * s2_2
      -- 2.4. def:even n := C(a, 2), from 2.3
      have s2_4 : Even (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k - 1), by parley_side⟩
      all_goals parley_side
    · skip
      -- 2.5. def:congruent-mod, from C2
      have s2_5 : (4 : ℤ) ∣ (a : ℤ) - 1 := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (1 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (1 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (1 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := (a : ℤ)) (b := (1 : ℤ)))).mp (by parley_side)
      -- 2.6. obtain k: def:divides d := 4, n := a − 1, from 2.5
      obtain ⟨k, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (a : ℤ) - 1))).mp (by parley_side)
      -- 2.7. algebra, from 1, 2.6
      have s2_7 : (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) = 2 * (k * (4 * k + 1)) := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s1 + ((1 / 2 : ℚ) * (a : ℚ) + 2 * (k : ℚ)) * s2_6
      -- 2.8. def:even n := C(a, 2), from 2.7
      have s2_8 : Even (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (Parley.Library.choose (a : ℤ) (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k + 1), by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoEven
