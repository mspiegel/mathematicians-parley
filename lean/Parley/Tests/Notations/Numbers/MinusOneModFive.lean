module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.MinusOneModFive

theorem minus_one_mod_five :
    (-1 : ℤ) % (5 : ℤ) = 4 := by
  -- 1. arithmetic
  have s1 : (-1 * 5 + 4 : ℤ) = -1 := by parley_arith
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * 5 + 4 = -1 := ⟨(-1 : ℤ), by norm_num⟩
  -- 3. mun:mod-remainder a := −1, m := 5, r := 4, from 2
  have r57_1 : (4 : ℤ) < 5 := by parley_arith
  exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := (5 : ℤ)) (by norm_num) (r := (4 : ℤ)) (by norm_num) (by norm_num))).mpr s2

end Parley.Tests.Notations.Numbers.MinusOneModFive
