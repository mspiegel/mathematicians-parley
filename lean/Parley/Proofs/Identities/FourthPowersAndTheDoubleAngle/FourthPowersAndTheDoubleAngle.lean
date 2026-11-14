module

public import InstanceTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.RingNF
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
  have s2 : 2 * x = x + x := by ring1
  -- 3. calculation
  calc Real.cos x ^ 4 - Real.sin x ^ 4 = (Real.cos x ^ 2 - Real.sin x ^ 2) * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring1
    _ = (Real.cos x ^ 2 - Real.sin x ^ 2) * 1 := congrArg (fun t : ℝ => (Real.cos x ^ 2 - Real.sin x ^ 2) * t) s1
    _ = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by ring_nf
    _ = Real.cos (x + x) := by
        have hI : Real.cos (x + x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))))
        exact hI.symm
    _ = Real.cos (2 * x) := congrArg (fun t : ℝ => Real.cos t) s2.symm

end Parley.Proofs.Identities.FourthPowersAndTheDoubleAngle.FourthPowersAndTheDoubleAngle
