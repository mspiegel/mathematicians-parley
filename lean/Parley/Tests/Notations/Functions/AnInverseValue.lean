module

public import Functions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AnInverseValue

theorem an_inverse_value (f : ℝ → ℝ) (hH1 : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) (hH2 : ∀ x : ℝ, f x = 2 * x + 1) :
    (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) 7 = 3 := by
  -- 1. mun:inverse-value, from H1
  have s1 : (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) (f 3) = 3 := by exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) hH1 (Set.mem_univ _))
  -- 2. instantiate x := 3 in H2
  have s2 : f 3 = 2 * 3 + 1 := by exact (hH2 (3 : ℝ))
  -- 3. calculation
  have s3 : f 3 = 7 := by
    calc f 3 = 2 * 3 + 1 := s2
      _ = 7 := by norm_num
  -- 4. substitute f(3) = 7 (line 3) into line 1
  exact Eq.subst (motive := (fun t : ℝ => (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) t = 3)) s3 s1

end Parley.Tests.Notations.Functions.AnInverseValue
