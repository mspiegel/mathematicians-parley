module

public import AlgebraTactics
public import ArithTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares

set_option maxHeartbeats 400000 in
theorem three_divides_sum_of_squares (p : ℤ) (q : ℤ) (hH3 : (3 : ℤ) ∣ p ^ 2 + q ^ 2) :
    (3 : ℤ) ∣ p := by
  -- the theorem. contradiction
  have sThm : (3 : ℤ) ∣ p := by
    by_contra hc_hS
    have hS : ¬ (3 : ℤ) ∣ p := by parley_suppose hc_hS
    -- 1. thm:square-mod-three n := p
    have s1 : (3 : ℤ) ∣ p ^ 2 ∨ (3 : ℤ) ∣ p ^ 2 - 1 := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p)) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p))).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p)) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p)) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p)); parley_side)
    -- 2. cases, from 1
    have s2 : (3 : ℤ) ∣ p ^ 2 - 1 := by
      rcases s1 with hC1 | hC2
      · skip
        -- 2.1. thm:three-divides-square n := p, from C1
        have s2_1 : (3 : ℤ) ∣ p := by first | exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) hC1) | exact ((Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) hC1)).symm | simpa using (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) hC1) | exact_mod_cast (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) hC1) | (have h := (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) hC1); parley_side)
        all_goals parley_side
      · skip
        all_goals parley_side
    -- 3. thm:square-mod-three n := q
    have s3 : (3 : ℤ) ∣ q ^ 2 ∨ (3 : ℤ) ∣ q ^ 2 - 1 := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q)) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q))).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q)) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q)) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q)); parley_side)
    -- 4. cases, from 3
    have s4 : (3 : ℤ) ∣ p := by
      rcases s3 with hC3 | hC4
      · skip
        -- 4.1. mun:divides-sum d := 3, a := p² − 1, b := q², from C3, 2
        have s4_1 : (3 : ℤ) ∣ p ^ 2 - 1 + q ^ 2 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3); parley_side)
        -- 4.2. mun:divides-difference d := 3, a := p² + q², b := p² − 1 + q², from H3, 4.1
        have s4_2 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 - (p ^ 2 - 1 + q ^ 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1); parley_side)
        -- 4.3. substitute
        have s4_3 : (3 : ℤ) ∣ (1 : ℤ) := by
          have c1 : p ^ 2 + q ^ 2 - (p ^ 2 - 1 + q ^ 2) = 1 := by parley_ring
          have row1 : (3 : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s4_2
          exact row1
        -- 4.4. thm:three-divides-no-small r := 1
        have r149_1 : (1 : ℤ) < 3 := by parley_arith
        have s4_4 : ¬ (3 : ℤ) ∣ (1 : ℤ) := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 1) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 1) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 1) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 1) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 1) (by parley_side) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 4.5. mun:divides-sum d := 3, a := p² − 1, b := q² − 1, from C4, 2
        have s4_5 : (3 : ℤ) ∣ p ^ 2 - 1 + (q ^ 2 - 1) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4); parley_side)
        -- 4.6. mun:divides-difference d := 3, a := p² + q², b := p² − 1 + (q² − 1), from H3, 4.5
        have s4_6 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 - (p ^ 2 - 1 + (q ^ 2 - 1)) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5); parley_side)
        -- 4.7. substitute
        have s4_7 : (3 : ℤ) ∣ (2 : ℤ) := by
          have c1 : p ^ 2 + q ^ 2 - (p ^ 2 - 1 + (q ^ 2 - 1)) = 2 := by parley_ring
          have row1 : (3 : ℤ) ∣ (2 : ℤ) := by parley_subst_at c1 s4_6
          exact row1
        -- 4.8. thm:three-divides-no-small r := 2
        have r167_1 : (2 : ℤ) < 3 := by parley_arith
        have s4_8 : ¬ (3 : ℤ) ∣ (2 : ℤ) := by first | exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 2) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 2) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 2) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 2) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := 2) (by parley_side) (by parley_side)); parley_side)
        all_goals parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares
