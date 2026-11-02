module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Tests.Notations.Numbers.SqrtFour

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SqrtFourNotIrrational

theorem sqrt_four_not_irrational :
    ¬ Irrational (Real.sqrt (4 : ℝ)) := by
  -- 1. thm:sqrt-four
  have s1 : Real.sqrt (4 : ℝ) = 2 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four | exact_mod_cast (Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four).symm | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; parley_int_power h) | (have h := Parley.Tests.Notations.Numbers.SqrtFour.sqrt_four; parley_side)
  -- 2. calculation
  have s2 : Real.sqrt (4 : ℝ) = 2 / 1 := by
    calc Real.sqrt (4 : ℝ) = 2 := by parley_side
      _ = 2 / 1 := by norm_num
  -- 3. def:rational x := √4, from 2
  have s3 : ∃ m : ℚ, (m : ℝ) = Real.sqrt (4 : ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.sqrt (4 : ℝ)))).mpr ⟨(2 : ℤ), 1, by parley_side, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.sqrt (4 : ℝ)))).mpr ⟨(2 : ℤ), 1, by parley_side, by parley_side⟩; parley_side)
  -- 4. contradiction
  have s4 : ¬ Irrational (Real.sqrt (4 : ℝ)) := by
    by_contra hc_hS
    have hS : Irrational (Real.sqrt (4 : ℝ)) := by parley_suppose hc_hS
    -- 4.1. def:irrational x := √4, from S
    have s4_1 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (4 : ℝ)) := by first | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (4 : ℝ)))).mp (by parley_side); parley_side)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Notations.Numbers.SqrtFourNotIrrational
