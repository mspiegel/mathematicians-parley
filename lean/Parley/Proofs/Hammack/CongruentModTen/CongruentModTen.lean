module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-mod-ten.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentModTen.CongruentModTen

theorem congruent_mod_ten (a : ℤ) (b : ℤ) :
    (a ≡ b [ZMOD (10 : ℤ)] ↔ a ≡ b [ZMOD (2 : ℤ)] ∧ a ≡ b [ZMOD (5 : ℤ)]) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. def:congruent-mod, from D1
    have s1 : (10 : ℤ) ∣ a - b := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mp hD1
    -- 2. obtain k: def:divides, from 1
    obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (10 : ℤ)) (n := a - b))).mp s1
    -- 3. algebra, from 2
    have s3 : a - b = 2 * (5 * k) := by linear_combination (norm := parley_norm) s2
    -- 4. def:divides d := 2, n := a − b, from 3
    have s4 : (2 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a - b))).mpr ⟨5 * k, s3⟩
    -- 5. def:congruent-mod, from 4
    have s5 : a ≡ b [ZMOD (2 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mpr s4
    -- 6. algebra, from 2
    have s6 : a - b = 5 * (2 * k) := by linear_combination (norm := parley_norm) s2
    -- 7. def:divides d := 5, n := a − b, from 6
    have s7 : (5 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := a - b))).mpr ⟨2 * k, s6⟩
    -- 8. def:congruent-mod, from 7
    have s8 : a ≡ b [ZMOD (5 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mpr s7
    -- 9. join 5, 8
    have s9 : a ≡ b [ZMOD (2 : ℤ)] ∧ a ≡ b [ZMOD (5 : ℤ)] := by parley_side
    exact ⟨(s9).1, (s9).2⟩
  · skip
    intro hD2
    -- 10. def:congruent-mod, from D2
    have s10 : (2 : ℤ) ∣ a - b := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (2 : ℤ)) (a := a) (b := b))).mp hD2.1
    -- 11. def:congruent-mod, from D2
    have s11 : (5 : ℤ) ∣ a - b := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := b))).mp hD2.2
    -- 12. obtain s: def:divides, from 10
    obtain ⟨s, s12⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a - b))).mp s10
    -- 13. obtain t: def:divides, from 11
    obtain ⟨t, s13⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := a - b))).mp s11
    -- 14. algebra, from 12
    have s14 : 5 * (a - b) = 10 * s := by linear_combination (norm := parley_norm) (5) * s12
    -- 15. algebra, from 13
    have s15 : 4 * (a - b) = 20 * t := by linear_combination (norm := parley_norm) (4) * s13
    -- 16. algebra, from 14, 15
    have s16 : a - b = 10 * (s - 2 * t) := by linear_combination (norm := parley_norm) s14 + (-1) * s15
    -- 17. def:divides d := 10, n := a − b, from 16
    have s17 : (10 : ℤ) ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (10 : ℤ)) (n := a - b))).mpr ⟨s - 2 * t, s16⟩
    -- 18. def:congruent-mod, from 17
    exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (10 : ℤ)) (a := a) (b := b))).mpr s17

end Parley.Proofs.Hammack.CongruentModTen.CongruentModTen
