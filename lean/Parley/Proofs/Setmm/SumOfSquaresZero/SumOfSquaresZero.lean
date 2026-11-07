module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/sum-of-squares-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SumOfSquaresZero.SumOfSquaresZero

set_option maxHeartbeats 400000 in
theorem sum_of_squares_zero (A : ℝ) (B : ℝ) :
    (A = 0 ∧ B = 0 ↔ A ^ 2 + B ^ 2 = 0) := by
  -- the theorem. both directions
  have sThm : A = 0 ∧ B = 0 ↔ A ^ 2 + B ^ 2 = 0 := by
    constructor
    · skip
      intro hD1
      -- 1. calculation
      have s1 : A ^ 2 + B ^ 2 = 0 := by
        calc A ^ 2 + B ^ 2 = 0 ^ 2 + B ^ 2 := by parley_subst hD1.1
          _ = 0 ^ 2 + 0 ^ 2 := by parley_subst hD1.2
          _ = 0 := by norm_num
      all_goals parley_side
    · skip
      intro hD2
      -- 2. mun:square-nonneg x := A
      have s2 : A ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A)); parley_side)
      -- 3. mun:square-nonneg x := B
      have s3 : B ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := B))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := B)); parley_side)
      -- 4. inequalities
      have s4 : A ^ 2 + B ^ 2 ≤ 0 := by parley_order
      -- 5. inequalities
      have s5 : -(B ^ 2) ≤ 0 := by parley_order
      -- 6. inequalities, from 4, 5
      have s6 : A ^ 2 ≤ 0 := by parley_order
      -- 7. antisymmetry, from 2, 6
      have s7 : A ^ 2 = 0 := by parley_side
      -- 8. inequalities
      have s8 : -(A ^ 2) ≤ 0 := by parley_order
      -- 9. inequalities, from 4, 8
      have s9 : B ^ 2 ≤ 0 := by parley_order
      -- 10. antisymmetry, from 3, 9
      have s10 : B ^ 2 = 0 := by parley_side
      -- 11. mun:square-zero x := A, from 7
      have s11 : A = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := A) (by parley_side))
      -- 12. mun:square-zero x := B, from 10
      have s12 : B = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := B) (by parley_side))
      -- 13. join 11, 12
      have s13 : A = 0 ∧ B = 0 := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.SumOfSquaresZero.SumOfSquaresZero
