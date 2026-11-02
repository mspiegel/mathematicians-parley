module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.HalfOrNextHalf

theorem half_or_next_half (N : ℤ) :
    ((∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) ∨ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2)) := by
  -- 1. mun:even-or-odd n := N
  have s1 : Even N ∨ Odd N := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N))
  -- 2. cases, from 1
  have s2 : (∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) ∨ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even n := N, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : (N : ℚ) / 2 = (k : ℚ) := by
        have s2_1_w : (N : ℚ) = 2 * (k : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_1; push_cast at h; linear_combination (norm := parley_norm) h
        linear_combination (norm := parley_norm) ((1) / ((2))) * s2_1_w
      -- 2.3. membership, from 2.2
      have s2_3 : ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2 := ⟨k, by first | (push_cast; linarith [s2_2]) | (rw [s2_2]; push_cast; ring) | (rw [← s2_2]; push_cast; ring) | exact s2_2 | exact s2_2.symm⟩
      -- 2.4. mun:or-left P := N/2 ∈ ℤ, Q := (N + 1)/2 ∈ ℤ, from 2.3
      have s2_4 : (∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) ∨ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side))
      all_goals parley_side
    · skip
      -- 2.5. obtain k: def:odd n := N, from C2
      obtain ⟨k, s2_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp (by parley_side)
      -- 2.6. algebra, from 2.5
      have s2_6 : ((N : ℚ) + 1) / 2 = (k : ℚ) + 1 := by
        have s2_5_w : (N : ℚ) = 2 * (k : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
        linear_combination (norm := parley_norm) ((1) / ((2))) * s2_5_w
      -- 2.7. membership, from 2.6
      have s2_7 : ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2 := ⟨k + 1, by first | (push_cast; linarith [s2_6]) | (rw [s2_6]; push_cast; ring) | (rw [← s2_6]; push_cast; ring) | exact s2_6 | exact s2_6.symm⟩
      -- 2.8. mun:or-right P := N/2 ∈ ℤ, Q := (N + 1)/2 ∈ ℤ, from 2.7
      have s2_8 : (∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) ∨ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := ∃ m : ℤ, (m : ℚ) = (N : ℚ) / 2) (Q := ∃ m : ℤ, (m : ℚ) = ((N : ℚ) + 1) / 2) (by parley_side))
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.Parity.HalfOrNextHalf
