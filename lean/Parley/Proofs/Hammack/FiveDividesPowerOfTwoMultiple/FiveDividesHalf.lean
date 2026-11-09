module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/five-divides-power-of-two-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf

theorem five_divides_half (b : ℤ) (hH2 : (5 : ℤ) ∣ 2 * b) :
    (5 : ℤ) ∣ b := by
  -- 1. mun:divides-self n := 5
  have s1 : (5 : ℤ) ∣ (5 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (5 : ℤ)))
  -- 2. mun:divides-combination e := 5, a := 2·b, b := 5, x := −2, y := b, from H2, 1
  have s2 : (5 : ℤ) ∣ 2 * b * -2 + 5 * b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (5 : ℤ)) (a := 2 * b) (b := (5 : ℤ)) (x := (-2 : ℤ)) (y := b) hH2 s1)
  -- 3. substitute
  have c1 : 2 * b * -2 + 5 * b = b := by parley_ring
  have row1 : (5 : ℤ) ∣ b := by parley_subst_at c1 s2
  exact row1

end Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf
