module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/seven-divides-four-times.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes

theorem seven_divides_four_times (a : ℤ) (hH2 : (7 : ℤ) ∣ 4 * a) :
    (7 : ℤ) ∣ a := by
  -- 1. obtain k: def:divides d := 7, n := 4a, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := 4 * a))).mp hH2
  -- 2. algebra, from 1
  have s2 : a = 7 * (2 * k - a) := by linear_combination (2) * s1
  -- 3. def:divides d := 7, n := a, from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mpr ⟨2 * k - a, s2⟩

end Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes
