module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula

/-! Written from proofs/hammack/choose-two-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoEven

theorem choose_two_even (a : ℤ) (hH1 : 0 ≤ a) (hH2 : a ≡ (0 : ℤ) [ZMOD (4 : ℤ)] ∨ a ≡ (1 : ℤ) [ZMOD (4 : ℤ)]) :
    Even (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) := by
  -- 1. thm:choose-two-formula n := a
  have s1 : (LeanBridges.Counting.choose a (2 : ℤ) : ℚ) = (a : ℚ) * ((a : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula.choose_two_formula (n := a) (by parley_side)); parley_side)
  -- 2. cases, from H2
  have s2 : Even (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) := by
    rcases hH2 with hC1 | hC2
    · skip
      -- 2.1. def:congruent-mod, from C1
      have s2_1 : (4 : ℤ) ∣ a := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (0 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (0 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (0 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (0 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (0 : ℤ)))).mp (by parley_side); parley_side)
      -- 2.2. obtain k: def:divides d := 4, n := a, from 2.1
      obtain ⟨k, s2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a))).mp (by parley_side)
      -- 2.3. algebra, from 1, 2.2
      have s2_3 : (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) = 2 * (k * (4 * k - 1)) := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s1 + ((1 / 2 : ℚ) * (a : ℚ) + 2 * (k : ℚ) - (1 / 2 : ℚ)) * s2_2
      -- 2.4. def:even n := C(a, 2), from 2.3
      have s2_4 : Even (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose a (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k - 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose a (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k - 1), by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 2.5. def:congruent-mod, from C2
      have s2_5 : (4 : ℤ) ∣ a - 1 := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (4 : ℤ)) (a := a) (b := (1 : ℤ)))).mp (by parley_side); parley_side)
      -- 2.6. obtain k: def:divides d := 4, n := a − 1, from 2.5
      obtain ⟨k, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a - 1))).mp (by parley_side)
      -- 2.7. algebra, from 1, 2.6
      have s2_7 : (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) = 2 * (k * (4 * k + 1)) := by qify at *; linear_combination (norm := parley_norm) ((2) / ((2))) * s1 + ((1 / 2 : ℚ) * (a : ℚ) + 2 * (k : ℚ)) * s2_6
      -- 2.8. def:even n := C(a, 2), from 2.7
      have s2_8 : Even (LeanBridges.Counting.choose a (2 : ℤ) : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose a (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose a (2 : ℤ) : ℤ)))).mpr ⟨k * (4 * k + 1), by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoEven
