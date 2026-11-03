module

public import Divisibility
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorOfInteger

/-! Written from proofs/setmm/remainder-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderZero.NoRemainderIsWholeQuotient

theorem no_remainder_is_whole_quotient (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    (LeanBridges.Divisibility.mod A B = 0 ↔ (∃ m : ℤ, (m : ℝ) = A / B)) := by
  -- 1. inequalities
  have s1 : B ≠ 0 := by parley_side
  set q : ℤ := ⌊A / B⌋ with hD1
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_side)
  -- 3. both directions
  have s3 : LeanBridges.Divisibility.mod A B = 0 ↔ (∃ m : ℤ, (m : ℝ) = A / B) := by
    constructor
    · skip
      intro hC1
      -- 3.1. substitute A mod B = A − B·q (line 2) into C1
      have s3_1 : A - B * (q : ℝ) = 0 := by parley_subst_at s2 hC1
      -- 3.2. algebra, from 3.1
      have r33_1 : B ≠ 0 := by parley_side
      have s3_2 : A / B = (q : ℝ) := by linear_combination (norm := parley_field) ((1) / ((B))) * s3_1
      -- 3.3. membership, from 3.2
      have s3_3 : ∃ m : ℤ, (m : ℝ) = A / B := ⟨q, by first | (push_cast; linarith [s3_2]) | (rw [s3_2]; push_cast; ring) | (rw [← s3_2]; push_cast; ring) | exact s3_2 | exact s3_2.symm⟩
      all_goals parley_side
    · skip
      intro hC2
      -- 3.4. calculation
      have s3_4 : (q : ℝ) = A / B := by
        calc (q : ℝ) = (⌊A / B⌋ : ℝ) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = A / B := by rw [← Classical.choose_spec hC2]; (first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))) | exact_mod_cast ((Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2)))).symm | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); parley_int_power h) | (have h := (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer (A := (Classical.choose hC2))); parley_side))
      -- 3.5. calculation
      have r48_1 : B ≠ 0 := by parley_side
      have s3_5 : LeanBridges.Divisibility.mod A B = 0 := by
        calc LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by parley_side
          _ = 0 := by linear_combination (norm := parley_field) (-B) * s3_4
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Setmm.RemainderZero.NoRemainderIsWholeQuotient
