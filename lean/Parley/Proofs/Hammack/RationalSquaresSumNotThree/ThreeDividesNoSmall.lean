module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall

theorem three_divides_no_small (r : ℤ) (hH1 : 0 < r) (hH2 : r < 3) :
    ¬ (3 : ℤ) ∣ r := by
  -- the theorem. contradiction
  intro hS
  -- 1. mun:divides-le e := 3, m := r, from S
  have s1 : 3 ≤ r := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (3 : ℤ)) (by parley_side) (m := r) (by parley_side) hS)
  -- 2. inequalities, from H2
  have s2 : ¬ 3 ≤ r := by parley_side
  exact s2 s1

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.ThreeDividesNoSmall
