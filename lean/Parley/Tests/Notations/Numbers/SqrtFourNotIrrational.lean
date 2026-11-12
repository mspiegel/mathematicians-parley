module

public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Parley.Items.Stdlib.Numbers
public import Parley.Tests.Notations.Numbers.SqrtFour

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SqrtFourNotIrrational

theorem sqrt_four_not_irrational :
    ¬ Irrational (Real.sqrt (4 : ℝ)) := by
  -- 1. thm:sqrt-four
  have s1 : Real.sqrt (4 : ℝ) = 2 := by exact Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four
  -- 2. calculation
  have s2 : Real.sqrt (4 : ℝ) = 2 / 1 := by
    calc Real.sqrt (4 : ℝ) = 2 := by exact s1
      _ = 2 / 1 := by norm_num
  -- 3. def:rational x := √4, from 2
  have s3 : ∃ m : ℚ, (m : ℝ) = Real.sqrt (4 : ℝ) := ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.sqrt (4 : ℝ)))).mpr ⟨(2 : ℤ), (1 : ℤ), by norm_num, by push_cast at s2 ⊢; exact s2⟩
  -- 4. contradiction
  intro hS
  -- 4.1. def:irrational x := √4, from S
  have s4_1 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (4 : ℝ)) := by exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp hS).2
  exact s4_1 s3

end Parley.Tests.Notations.Numbers.SqrtFourNotIrrational
