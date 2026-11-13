module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.AChoiceOutOfRange

theorem a_choice_out_of_range :
    (LeanBridges.Counting.choose (3 : ℤ) (5 : ℤ) : ℤ) = 0 := by
  -- 1. def:C n := 3, k := 5
  have r64_1 : (3 : ℤ) < 5 := by parley_arith
  exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (3 : ℤ)) (by norm_num) (k := (5 : ℤ))) (by norm_num)

end Parley.Tests.Docs.Grammar.AChoiceOutOfRange
