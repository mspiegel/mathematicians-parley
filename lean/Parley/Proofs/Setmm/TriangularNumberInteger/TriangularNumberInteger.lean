module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/triangular-number-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger

theorem triangular_number_integer (n : ℤ) :
    (∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  have s2 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. obtain k: def:even, from C1
      obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
      -- 2.2. algebra, from 2.1
      have s2_2 : (n : ℚ) * ((n : ℚ) + 1) / 2 = (k : ℚ) * (2 * (k : ℚ) + 1) := by
        have s2_1_w : (n : ℚ) = 2 * (k : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_1; push_cast at h; linear_combination h
        linear_combination ((2 * (k : ℚ) + (n : ℚ) + 1) / ((2))) * s2_1_w
      -- 2.3. membership, from 2.2
      have s2_3 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := ⟨k * (2 * k + 1), by push_cast; linarith [s2_2]⟩
      all_goals parley_side
    · skip
      -- 2.4. obtain k: def:odd, from C2
      obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
      -- 2.5. algebra, from 2.4
      have s2_5 : (n : ℚ) * ((n : ℚ) + 1) / 2 = (2 * (k : ℚ) + 1) * ((k : ℚ) + 1) := by
        have s2_4_w : (n : ℚ) = 2 * (k : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination h
        linear_combination ((2 * (k : ℚ) + (n : ℚ) + 2) / ((2))) * s2_4_w
      -- 2.6. membership, from 2.5
      have s2_6 : ∃ m : ℤ, (m : ℚ) = (n : ℚ) * ((n : ℚ) + 1) / 2 := ⟨(2 * k + 1) * (k + 1), by push_cast; linarith [s2_5]⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger
