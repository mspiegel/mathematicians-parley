module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/polynomial-sign.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PolynomialSign.NegativePowers

theorem negative_powers (x : ℝ) (hH2 : x < 0) :
    x ^ 2 ≥ 0 ∧ x ^ 3 ≤ 0 ∧ x ^ 4 ≥ 0 ∧ x ^ 5 ≤ 0 := by
  -- 1. inequalities
  have s1 : -x ≥ 0 := by linarith only [hH2]
  -- 2. mun:square-nonneg
  have s2 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 3. mun:product-nonneg x := x², y := −x, from 1, 2
  have s3 : x ^ 2 * -x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 2) (y := -x) s2 s1)
  -- 4. inequalities
  have s4 : x ^ 3 ≤ 0 := by linarith only [s3]
  -- 5. mun:square-nonneg x := x²
  have s5 : (x ^ 2) ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x ^ 2))
  -- 6. algebra
  have s6 : x ^ 4 = (x ^ 2) ^ 2 := by parley_ring
  -- 7. transitivity, from 6, 5
  have s7 : x ^ 4 ≥ 0 := by exact LE.le.trans_eq s5 s6.symm
  -- 8. mun:product-nonneg x := x⁴, y := −x, from 1, 7
  have s8 : x ^ 4 * -x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 4) (y := -x) s7 s1)
  -- 9. inequalities
  have s9 : x ^ 5 ≤ 0 := by linarith only [s8]
  -- 10. join 2, 4, 7, 9
  have s10a : x ^ 2 ≥ 0 := s2
  have s10b : x ^ 3 ≤ 0 := s4
  have s10c : x ^ 4 ≥ 0 := s7
  have s10d : x ^ 5 ≤ 0 := s9
  exact ⟨s10a, s10b, s10c, s10d⟩

end Parley.Proofs.Hammack.PolynomialSign.NegativePowers
