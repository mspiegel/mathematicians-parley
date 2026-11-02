module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AHypothesisFromTheLineCited

theorem a_hypothesis_from_the_line_cited (k : ℕ) (hH1 : 0 < k) :
    ((LeanBridges.Counting.factorial (k : ℤ) : ℤ) ≠ 0 ∧ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * (k : ℤ) ≠ 0) := by
  -- 1. mun:factorial-nonzero n := k
  have s1 : (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := k)); parley_side)
  -- 2. mun:factorial-nat n := k
  have s2 : 0 < (LeanBridges.Counting.factorial (k : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)); parley_side)
  -- 3. thm:product-nonzero x := k!, y := k, from H1, 2
  have s3 : (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * (k : ℤ) ≠ 0 := by first | exact (Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side)) | exact ((Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero.product_nonzero (x := (LeanBridges.Counting.factorial (k : ℤ) : ℝ)) (y := (k : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 4. join 1, 3
  have s4 : (LeanBridges.Counting.factorial (k : ℤ) : ℤ) ≠ 0 ∧ (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * (k : ℤ) ≠ 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapes.AHypothesisFromTheLineCited
