module

public import AlgebraTactics
public import InstanceTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/fourth-powers-and-the-double-angle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.FourthPowersAndTheDoubleAngle.FourthPowersAndTheDoubleAngle

theorem fourth_powers_and_the_double_angle (x : ℝ) :
    Real.cos x ^ 4 - Real.sin x ^ 4 = Real.cos (2 * x) := by
  -- 1. mun:sin-cos-squares a := x
  have s1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    have hI : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))))
    exact hI
  -- 2. algebra
  have s2 : 2 * x = x + x := by parley_ring
  -- 3. calculation
  calc Real.cos x ^ 4 - Real.sin x ^ 4 = (Real.cos x ^ 2 - Real.sin x ^ 2) * (Real.sin x ^ 2 + Real.cos x ^ 2) := by parley_ring
    _ = (Real.cos x ^ 2 - Real.sin x ^ 2) * 1 := by parley_subst s1
    _ = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by parley_ring
    _ = Real.cos (x + x) := by
        have hI : Real.cos (x + x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))))
        exact hI.symm
    _ = Real.cos (2 * x) := by parley_subst s2

end Parley.Proofs.Identities.FourthPowersAndTheDoubleAngle.FourthPowersAndTheDoubleAngle
