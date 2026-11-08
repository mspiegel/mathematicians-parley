module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd

theorem power_of_three_odd (n : ℤ) (hH1 : 0 ≤ n) :
    Odd (3 ^ n.toNat : ℤ) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → Odd (3 ^ j.toNat : ℤ) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (3 ^ 0 : ℤ) = 2 * 0 + 1 := by parley_arith
      -- 1.2. def:odd n := 3^0, from 1.1
      have s1_2 : Odd (3 ^ 0 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ 0 : ℤ)))).mpr ⟨(0 : ℤ), s1_1⟩
      simpa using s1_2
    | succ j hK hIH =>
      -- 1.3. obtain k: def:odd n := 3^j, from IH
      obtain ⟨k, s1_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ j.toNat : ℤ)))).mp hIH
      -- 1.4. calculation
      have s1_4 : 3 ^ (j + 1).toNat = 2 * (3 * k + 1) + 1 := by
        calc (3 ^ (j + 1).toNat : ℤ) = 3 ^ j.toNat * 3 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := j) (by parley_side))
          _ = (2 * k + 1) * 3 := by parley_subst s1_3
          _ = 2 * (3 * k + 1) + 1 := by parley_ring
      -- 1.5. def:odd n := 3^(j + 1), from 1.4
      exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 ^ (j + 1).toNat : ℤ)))).mpr ⟨3 * k + 1, s1_4⟩
  -- 2. instantiate j := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd
