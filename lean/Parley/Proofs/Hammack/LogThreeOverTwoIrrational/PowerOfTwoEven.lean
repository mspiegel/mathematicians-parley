module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven

theorem power_of_two_even (n : ℤ) (hH1 : 0 < n) :
    Even (2 ^ n.toNat : ℤ) := by
  -- 1. mun:nat-minus-one
  have s1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))
  -- 2. mun:exponent-step a := 2, m := n − 1, from 1
  have s2 : (2 ^ (n - 1 + 1) : ℚ) = 2 ^ (n - 1) * 2 := by (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); simp only [parley_zpow_toNat (n := n - 1 + 1) (h := add_nonneg (s1) (by norm_num)), parley_zpow_toNat (n := n - 1) (h := s1)] at h ⊢; exact_mod_cast h)
  -- 3. substitute
  have s3 : (2 ^ n.toNat : ℚ) = 2 ^ (n - 1) * 2 := by
    have c1 : n - 1 + 1 = n := by parley_ring
    have row1 : (2 ^ n.toNat : ℚ) = 2 ^ (n - 1) * 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (2 ^ t : ℚ) = 2 ^ (n - 1) * 2)) c1 s2; simp only [parley_zpow_toNat (n := n) (h := le_of_lt hH1), parley_zpow_toNat (n := n - 1) (h := s1)] at h ⊢; exact_mod_cast h)
    exact row1
  -- 4. algebra, from 3
  have s4 : (2 ^ n.toNat : ℚ) = 2 * 2 ^ (n - 1) := by linear_combination (norm := parley_norm) s3
  -- 5. mun:power-integer a := 2, m := n − 1, from 1
  have s5 : ∃ m : ℤ, (m : ℚ) = 2 ^ (n - 1) := by
    have whole1 : ((2 : ℚ) : ℚ) ^ (n - 1).toNat = (2 ^ (n - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
    exact ⟨(((2 : ℤ) ^ (n - 1).toNat) : ℤ), by (push_cast; simp only [whole1]; all_goals ring)⟩
  -- 6. def:even n := 2^n, from 4, 5
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (2 ^ n.toNat : ℤ)))).mpr ⟨Classical.choose s5, by have := Classical.choose_spec s5; parley_side⟩

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven
