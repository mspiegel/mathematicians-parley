module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-mod-ten.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentModTen.CongruentModTen

theorem congruent_mod_ten (a : ℤ) (b : ℤ) :
    (a ≡ b [ZMOD (10 : ℤ)] ↔ a ≡ b [ZMOD (2 : ℤ)] ∧ a ≡ b [ZMOD (5 : ℤ)]) := by
  -- the theorem. both directions
  have sThm : a ≡ b [ZMOD (10 : ℤ)] ↔ a ≡ b [ZMOD (2 : ℤ)] ∧ a ≡ b [ZMOD (5 : ℤ)] := by
    constructor
    · skip
      intro hD1
      -- 1. def:congruent-mod, from D1
      have s1 : (10 : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mp (by parley_side)
      -- 2. obtain k: def:divides, from 1
      obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (10 : ℤ)) (n := a - b))).mp (by parley_side)
      -- 3. algebra, from 2
      have s3 : a - b = 2 * (5 * k) := by linear_combination (norm := parley_norm) s2
      -- 4. def:divides d := 2, n := a − b, from 3
      have s4 : (2 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a - b))).mpr ⟨5 * k, by parley_side⟩
      -- 5. def:congruent-mod, from 4
      have s5 : a ≡ b [ZMOD (2 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mpr (by parley_side)
      -- 6. algebra, from 2
      have s6 : a - b = 5 * (2 * k) := by linear_combination (norm := parley_norm) s2
      -- 7. def:divides d := 5, n := a − b, from 6
      have s7 : (5 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := a - b))).mpr ⟨2 * k, by parley_side⟩
      -- 8. def:congruent-mod, from 7
      have s8 : a ≡ b [ZMOD (5 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mpr (by parley_side)
      -- 9. join 5, 8
      have s9 : a ≡ b [ZMOD (2 : ℤ)] ∧ a ≡ b [ZMOD (5 : ℤ)] := by parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 10. def:congruent-mod, from D2
      have s10 : (2 : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mp (by parley_side)
      -- 11. def:congruent-mod, from D2
      have s11 : (5 : ℤ) ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mp (by parley_side)
      -- 12. obtain s: def:divides, from 10
      obtain ⟨s, s12⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a - b))).mp (by parley_side)
      -- 13. obtain t: def:divides, from 11
      obtain ⟨t, s13⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := a - b))).mp (by parley_side)
      -- 14. algebra, from 12
      have s14 : 5 * (a - b) = 10 * s := by linear_combination (norm := parley_norm) (5) * s12
      -- 15. algebra, from 13
      have s15 : 4 * (a - b) = 20 * t := by linear_combination (norm := parley_norm) (4) * s13
      -- 16. algebra, from 14, 15
      have s16 : a - b = 10 * (s - 2 * t) := by linear_combination (norm := parley_norm) s14 + (-1) * s15
      -- 17. def:divides d := 10, n := a − b, from 16
      have s17 : (10 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (10 : ℤ)) (n := a - b))).mpr ⟨s - 2 * t, by parley_side⟩
      -- 18. def:congruent-mod, from 17
      have s18 : a ≡ b [ZMOD (10 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mpr (by parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CongruentModTen.CongruentModTen
