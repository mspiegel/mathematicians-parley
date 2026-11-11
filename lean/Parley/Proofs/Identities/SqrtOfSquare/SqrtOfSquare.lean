module

public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/sqrt-of-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtOfSquare.SqrtOfSquare

theorem sqrt_of_square (x : ℝ) :
    Real.sqrt (x ^ 2) = abs x := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 2. def:sqrt x := x², from 1
  have s2a : Real.sqrt (x ^ 2) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x ^ 2) s1)
  have s2b : Real.sqrt (x ^ 2) ^ 2 = x ^ 2 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x ^ 2) s1)
  -- 3. mun:abs-nonneg
  have s3 : abs x ≥ 0 := by
    have hI : 0 ≤ abs x := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))))
    exact hI
  -- 4. calculation
  have s4 : Real.sqrt (x ^ 2) ^ 2 = abs x ^ 2 := by
    calc Real.sqrt (x ^ 2) ^ 2 = x ^ 2 := by exact s2b
      _ = abs x ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)).symm
  -- 5. mun:square-equal x := √(x²), y := |x|, from 2, 3, 4
  exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) s2a s3)).mp s4

end Parley.Proofs.Identities.SqrtOfSquare.SqrtOfSquare
