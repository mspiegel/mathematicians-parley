module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.MinusOneFourModFive

theorem minus_one_four_mod_five :
    (-1 : ℤ) ≡ (4 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  have s1 : (-1 - 4 : ℤ) = 5 * -1 := by norm_num
  -- 2. def:divides d := 5, n := −1 − 4, from 1
  have s2 : (5 : ℤ) ∣ (-1 - 4 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := (-1 - 4 : ℤ)))).mpr ⟨(-1 : ℤ), by norm_num⟩
  -- 3. def:congruent-mod n := 5, a := −1, b := 4, from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := (-1 : ℤ)) (b := (4 : ℤ)))).mpr s2

end Parley.Tests.Notations.Divisibility.MinusOneFourModFive
