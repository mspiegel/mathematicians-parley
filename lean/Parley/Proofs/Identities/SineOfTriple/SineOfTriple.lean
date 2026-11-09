module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/sine-of-triple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineOfTriple.SineOfTriple

theorem sine_of_triple (x : ℝ) :
    Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
  -- 1. algebra
  have s1 : 2 * x = x + x := by parley_ring
  -- 2. calculation
  have s2 : Real.sin (2 * x) = Real.sin x * Real.cos x + Real.cos x * Real.sin x := by
    calc Real.sin (2 * x) = Real.sin (x + x) := by parley_subst s1
      _ = Real.sin x * Real.cos x + Real.cos x * Real.sin x := by
          have hI : Real.sin (x + x) = Real.sin x * Real.cos x + Real.cos x * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))))
          exact hI
  -- 3. calculation
  have s3 : Real.cos (2 * x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by
    calc Real.cos (2 * x) = Real.cos (x + x) := by parley_subst s1
      _ = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by
          have hI : Real.cos (x + x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))))
          exact hI
  -- 4. algebra
  have s4 : 3 * x = 2 * x + x := by parley_ring
  -- 5. mun:sin-cos-squares a := x
  have s5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    have hI : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))))
    exact hI
  -- 6. calculation
  calc Real.sin (3 * x) = Real.sin (2 * x + x) := by parley_subst s4
    _ = Real.sin (2 * x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by
        have hI : Real.sin (2 * x + x) = Real.sin (2 * x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))))
        exact hI
    _ = (Real.sin x * Real.cos x + Real.cos x * Real.sin x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by parley_subst s2
    _ = (Real.sin x * Real.cos x + Real.cos x * Real.sin x) * Real.cos x + (Real.cos x * Real.cos x - Real.sin x * Real.sin x) * Real.sin x := by parley_subst s3
    _ = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by linear_combination (norm := parley_norm) (3 * Real.sin x) * s5

end Parley.Proofs.Identities.SineOfTriple.SineOfTriple
