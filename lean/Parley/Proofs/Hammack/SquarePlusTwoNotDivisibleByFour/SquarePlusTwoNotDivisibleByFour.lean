module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween

/-! Written from proofs/hammack/square-plus-two-not-divisible-by-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquarePlusTwoNotDivisibleByFour.SquarePlusTwoNotDivisibleByFour

theorem square_plus_two_not_divisible_by_four (n : ℤ) :
    ¬ (4 : ℤ) ∣ n ^ 2 + 2 := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain m: def:divides d := 4, n := n² + 2, from S
  obtain ⟨m, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := n ^ 2 + 2))).mp hS
  -- 2. mun:even-or-odd
  have s2 : Even n ∨ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 3. cases, from 2
  have s3 : n ^ 2 + 2 ≠ 4 * m := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. obtain k: def:even, from C1
      obtain ⟨k, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp hC1
      -- 3.2. substitute n = 2k (line 3.1) into line 1
      have s3_2 : (2 * k) ^ 2 + 2 = 4 * m := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 + 2 = 4 * m)) s3_1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 3.3. algebra, from 3.2
      have s3_3 : 4 * (m - k ^ 2) = 2 := by linear_combination (norm := parley_norm) (-1) * s3_2
      -- 3.4. thm:four-times-between j := m − k², r := 2
      have r38_1 : (2 : ℤ) > 0 := by parley_arith
      have r38_2 : (2 : ℤ) < 4 := by parley_arith
      have s3_4 : 4 * (m - k ^ 2) ≠ 2 := by exact (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2) (r := (2 : ℤ)) r38_1 r38_2)
      exact absurd s3_3 s3_4
    · skip
      -- 3.5. obtain k: def:odd, from C2
      obtain ⟨k, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hC2
      -- 3.6. substitute n = 2k + 1 (line 3.5) into line 1
      have s3_6 : (2 * k + 1) ^ 2 + 2 = 4 * m := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 + 2 = 4 * m)) s3_5 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 3.7. algebra, from 3.6
      have s3_7 : 4 * (m - k ^ 2 - k) = 3 := by linear_combination (norm := parley_norm) (-1) * s3_6
      -- 3.8. thm:four-times-between j := m − k² − k, r := 3
      have r55_1 : (3 : ℤ) > 0 := by parley_arith
      have r55_2 : (3 : ℤ) < 4 := by parley_arith
      have s3_8 : 4 * (m - k ^ 2 - k) ≠ 3 := by exact (Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween.four_times_between (j := m - k ^ 2 - k) (r := (3 : ℤ)) r55_1 r55_2)
      exact absurd s3_7 s3_8
  -- 4. restate 3
  have s4 : n ^ 2 + 2 ≠ 4 * m := by parley_side
  exact s4 s1

end Parley.Proofs.Hammack.SquarePlusTwoNotDivisibleByFour.SquarePlusTwoNotDivisibleByFour
