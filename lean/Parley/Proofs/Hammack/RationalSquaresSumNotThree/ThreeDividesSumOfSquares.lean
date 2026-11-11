module

public import AlgebraTactics
public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree
public import Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares

theorem three_divides_sum_of_squares (p : ℤ) (q : ℤ) (hH3 : (3 : ℤ) ∣ p ^ 2 + q ^ 2) :
    (3 : ℤ) ∣ p := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. thm:square-mod-three n := p
  have s1 : (3 : ℤ) ∣ p ^ 2 ∨ (3 : ℤ) ∣ p ^ 2 - 1 := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := p))
  -- 2. cases, from 1
  have s2 : (3 : ℤ) ∣ p ^ 2 - 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. thm:three-divides-square n := p, from C1
      have s2_1 : (3 : ℤ) ∣ p := by exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) (by parley_side))
      exact absurd s2_1 hS
    · skip
      exact hC2
  -- 3. thm:square-mod-three n := q
  have s3 : (3 : ℤ) ∣ q ^ 2 ∨ (3 : ℤ) ∣ q ^ 2 - 1 := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree.square_mod_three (n := q))
  -- 4. cases, from 3
  have s4 : (3 : ℤ) ∣ p := by
    rcases s3 with hC3 | hC4
    · skip
      -- 4.1. mun:divides-sum d := 3, a := p² − 1, b := q², from C3, 2
      have s4_1 : (3 : ℤ) ∣ p ^ 2 - 1 + q ^ 2 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2) s2 hC3)
      -- 4.2. mun:divides-difference d := 3, a := p² + q², b := p² − 1 + q², from H3, 4.1
      have s4_2 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 - (p ^ 2 - 1 + q ^ 2) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + q ^ 2) hH3 s4_1)
      -- 4.3. substitute
      have s4_3 : (3 : ℤ) ∣ (1 : ℤ) := by
        have c1 : p ^ 2 + q ^ 2 - (p ^ 2 - 1 + q ^ 2) = 1 := by parley_ring
        have row1 : (3 : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) c1 s4_2; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.4. thm:three-divides-no-small r := 1
      have r149_1 : (1 : ℤ) < 3 := by parley_arith
      have s4_4 : ¬ (3 : ℤ) ∣ (1 : ℤ) := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := (1 : ℤ)) (by parley_side) r149_1)
      exact absurd s4_3 s4_4
    · skip
      -- 4.5. mun:divides-sum d := 3, a := p² − 1, b := q² − 1, from C4, 2
      have s4_5 : (3 : ℤ) ∣ p ^ 2 - 1 + (q ^ 2 - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (3 : ℤ)) (a := p ^ 2 - 1) (b := q ^ 2 - 1) s2 hC4)
      -- 4.6. mun:divides-difference d := 3, a := p² + q², b := p² − 1 + (q² − 1), from H3, 4.5
      have s4_6 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 - (p ^ 2 - 1 + (q ^ 2 - 1)) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (3 : ℤ)) (a := p ^ 2 + q ^ 2) (b := p ^ 2 - 1 + (q ^ 2 - 1)) hH3 s4_5)
      -- 4.7. substitute
      have s4_7 : (3 : ℤ) ∣ (2 : ℤ) := by
        have c1 : p ^ 2 + q ^ 2 - (p ^ 2 - 1 + (q ^ 2 - 1)) = 2 := by parley_ring
        have row1 : (3 : ℤ) ∣ (2 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) c1 s4_6; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.8. thm:three-divides-no-small r := 2
      have r167_1 : (2 : ℤ) < 3 := by parley_arith
      have s4_8 : ¬ (3 : ℤ) ∣ (2 : ℤ) := by exact (Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall.three_divides_no_small (r := (2 : ℤ)) (by parley_side) r167_1)
      exact absurd s4_7 s4_8
  exact hS s4

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesSumOfSquares
