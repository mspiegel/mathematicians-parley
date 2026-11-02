module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween

/-! Written from proofs/hammack/square-plus-two-not-divisible-by-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquarePlusTwoNotDivisibleByFour.SquarePlusTwoNotDivisibleByFour

theorem square_plus_two_not_divisible_by_four (n : ℤ) :
    ¬ (4 : ℤ) ∣ n ^ 2 + 2 := by
  -- the theorem. contradiction
  have sThm : ¬ (4 : ℤ) ∣ n ^ 2 + 2 := by
    by_contra hc_hS
    have hS : (4 : ℤ) ∣ n ^ 2 + 2 := by parley_suppose hc_hS
    -- 1. obtain m: def:divides d := 4, n := n² + 2, from S
    obtain ⟨m, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2 + 2))).mp (by parley_side)
    -- 2. mun:even-or-odd
    have s2 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)); parley_side)
    -- 3. cases, from 2
    have s3 : n ^ 2 + 2 ≠ 4 * m := by
      rcases s2 with hC1 | hC2
      · skip
        -- 3.1. obtain k: def:even, from C1
        obtain ⟨k, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp (by parley_side)
        -- 3.2. substitute n = 2k (line 3.1) into line 1
        have s3_2 : (2 * k) ^ 2 + 2 = 4 * m := by parley_subst_at s3_1 s1
        -- 3.3. algebra, from 3.2
        have s3_3 : 4 * (m - k ^ 2) = 2 := by linear_combination (norm := parley_norm) (-1) * s3_2
        -- 3.4. thm:four-times-between j := m − k², r := 2
        have r38_1 : (2 : ℤ) > 0 := by parley_arith
        have r38_2 : (2 : ℤ) < 4 := by parley_arith
        have s3_4 : 4 * (m - k ^ 2) ≠ 2 := by first | exact (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) (by parley_side) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 3.5. obtain k: def:odd, from C2
        obtain ⟨k, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
        -- 3.6. substitute n = 2k + 1 (line 3.5) into line 1
        have s3_6 : (2 * k + 1) ^ 2 + 2 = 4 * m := by parley_subst_at s3_5 s1
        -- 3.7. algebra, from 3.6
        have s3_7 : 4 * (m - k ^ 2 - k) = 3 := by linear_combination (norm := parley_norm) (-1) * s3_6
        -- 3.8. thm:four-times-between j := m − k² − k, r := 3
        have r55_1 : (3 : ℤ) > 0 := by parley_arith
        have r55_2 : (3 : ℤ) < 4 := by parley_arith
        have s3_8 : 4 * (m - k ^ 2 - k) ≠ 3 := by first | exact (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) (by parley_side) (by parley_side)); parley_side)
        all_goals parley_side
    -- 4. restate 3
    have s4 : n ^ 2 + 2 ≠ 4 * m := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquarePlusTwoNotDivisibleByFour.SquarePlusTwoNotDivisibleByFour
