module

public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne

/-! Written from tests/elaborator/a-define-filling-a-cited-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineFillingACitedFunction.ADefineFillingACitedFunction

theorem a_define_filling_a_cited_function (t : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → t j = j + 1) :
    t 1 = 1 + 1 := by
  -- 1. D1
  have s1 : ∀ j : ℤ, 0 < j → t j = j + 1 := by (try simp only [hD1]); first | done | parley_side
  -- 2. thm:value-at-one f := t, from 1
  first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by parley_side)); parley_side)

end Parley.Tests.Elaborator.ADefineFillingACitedFunction.ADefineFillingACitedFunction
