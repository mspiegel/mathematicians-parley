module

public import Divisibility
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/difference-remainder-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceRemainderZero.DifferenceRemainderZero

theorem difference_remainder_zero (A : ℤ) (B : ℤ) (N : ℕ) (hH3 : 0 < N) :
    ((A - B) % (N : ℤ) = 0 ↔ A % (N : ℤ) = B % (N : ℤ)) := by
  -- the theorem. both directions
  have sThm : (A - B) % (N : ℤ) = 0 ↔ A % (N : ℤ) = B % (N : ℤ) := by
    constructor
    · skip
      intro hC1
      -- 1. obtain q: mun:mod-remainder a := A − B, m := N, r := 0, from C1
      have r20_1 : 0 < (N : ℤ) := by parley_order
      obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side)
      -- 2. mun:mod-multiple r := B, m := N
      have s2 : (q * (N : ℤ) + B) % (N : ℤ) = B % (N : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q)); parley_side)
      -- 3. substitute
      have s3 : A % (N : ℤ) = B % (N : ℤ) := by
        have c1 : q * (N : ℤ) + B = A := by linear_combination (norm := parley_norm) s1
        have row1 : A % (N : ℤ) = B % (N : ℤ) := by parley_subst_at c1 s2
        exact row1
      all_goals parley_side
    · skip
      intro hC2
      -- 4. mun:mod-equal-congruent, from C2
      have s4 : A ≡ B [ZMOD (N : ℤ)] := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) (by parley_side)); parley_side)
      -- 5. def:congruent-mod, from 4
      have s5 : (N : ℤ) ∣ A - B := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (N : ℤ)) (a := A) (b := B))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (N : ℤ)) (a := A) (b := B))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (N : ℤ)) (a := A) (b := B))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (N : ℤ)) (a := A) (b := B))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (N : ℤ)) (a := A) (b := B))).mp (by parley_side); parley_side)
      -- 6. obtain k: def:divides d := N, n := A − B, from 5
      obtain ⟨k, s6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (N : ℤ)) (n := A - B))).mp (by parley_side)
      -- 7. algebra, from 6
      have s7 : k * (N : ℤ) = A - B := by linear_combination (norm := parley_norm) (-1) * s6
      -- 8. exhibit, from 7
      have s8 : ∃ q : ℤ, q * (N : ℤ) = A - B := ⟨k, by parley_side⟩
      -- 9. mun:mod-remainder a := A − B, m := N, r := 0, from 8
      have r50_1 : 0 < (N : ℤ) := by parley_order
      have s9 : (A - B) % (N : ℤ) = 0 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := 0) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := 0) (by parley_side))).mpr (by parley_side); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.DifferenceRemainderZero.DifferenceRemainderZero
