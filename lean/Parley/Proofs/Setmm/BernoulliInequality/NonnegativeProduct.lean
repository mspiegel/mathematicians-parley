module

public import NormTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/bernoulli-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct

theorem nonnegative_product (x : ℝ) (y : ℝ) (hH3 : 0 ≤ x) (hH4 : 0 ≤ y) :
    0 ≤ x * y := by
  -- 1. axi:trichotomy
  have s1 : (x < 0 ∨ x = 0) ∨ 0 < x := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x))
  -- 2. cases, from 1
  rcases s1 with (hC1 | hC2) | hC3
  · skip
    -- 2.1. inequalities, from C1
    have s2_1 : ¬ 0 ≤ x := by linarith only [hC1]
    exact absurd hH3 s2_1
  · skip
    -- 2.2. algebra, from C2
    have s2_2 : x * y = 0 := by linear_combination (norm := parley_norm) (y) * hC2
    -- 2.3. inequalities
    linarith only [s2_2]
  · skip
    -- 2.4. mun:multiply-le x := 0, c := x, from C3, H4
    have s2_4 : x * 0 ≤ x * y := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := y) (c := x) hH4 hC3)
    -- 2.5. inequalities, from 2.4
    linarith only [s2_4]

end Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct
