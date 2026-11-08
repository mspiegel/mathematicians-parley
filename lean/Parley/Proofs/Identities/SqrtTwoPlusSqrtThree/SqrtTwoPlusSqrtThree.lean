module

public import AlgebraTactics
public import ArithTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational
public import Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
public import Parley.Proofs.Setmm.RationalClosure.IrrationalSum
public import Parley.Proofs.Setmm.RationalClosure.RationalProduct

/-! Written from proofs/identities/sqrt-two-plus-sqrt-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtTwoPlusSqrtThree.SqrtTwoPlusSqrtThree

theorem sqrt_two_plus_sqrt_three :
    Irrational (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) := by
  -- 1. thm:sqrt6-irrational
  have s1 : Irrational (Real.sqrt (6 : ℝ)) := by exact Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational.sqrt6_irrational
  -- 2. thm:irrational-product A := √6, B := 2, from 1
  have r16_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s2 : Irrational (Real.sqrt (6 : ℝ) * 2) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (6 : ℝ)) (B := (2 : ℚ)) (by parley_side) s1); parley_side)
  -- 3. thm:irrational-sum A := √6·2, B := 5, from 2
  have s3 : Irrational (Real.sqrt (6 : ℝ) * 2 + 5) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (6 : ℝ) * 2) (B := (5 : ℚ)) s2); parley_side)
  -- 4. contradiction
  have s4 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) := by
    intro hS
    -- 4.1. thm:rational-product A := √2 + √3, B := √2 + √3, from S
    have s4_1 : ∃ m : ℚ, (m : ℝ) = (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) * (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) := by (exact ⟨(Classical.choose hS : ℚ) * (Classical.choose hS : ℚ), by push_cast; (try simp only [Classical.choose_spec hS]); first | done | parley_ring⟩)
    -- 4.2. substitute
    have s4_2 : ∃ m : ℚ, (m : ℝ) = (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) ^ 2 := by
      have c1 : (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) * (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) = (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) ^ 2 := by parley_real
      have row1 : ∃ m : ℚ, (m : ℝ) = (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) ^ 2 := by parley_subst_at c1 s4_1
      exact row1
    -- 4.3. substitute
    have s4_3 : ∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ) * 2 + 5 := by
      have c1 : (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) ^ 2 = Real.sqrt (6 : ℝ) * 2 + 5 := by parley_real
      have row1 : ∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ) * 2 + 5 := by parley_subst_at c1 s4_2
      exact row1
    -- 4.4. def:irrational x := √6·2 + 5, from 3
    have s4_4 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ) * 2 + 5) := (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (6 : ℝ) * 2 + 5))).mp s3).2
    -- 4.5. restate 4.4
    have s4_5 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ) * 2 + 5) := by parley_side
    exact s4_5 s4_3
  -- 5. def:irrational x := √2 + √3, from 4
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)))).mpr (by parley_side)

end Parley.Proofs.Identities.SqrtTwoPlusSqrtThree.SqrtTwoPlusSqrtThree
