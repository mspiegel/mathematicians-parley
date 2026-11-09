module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/divisible-by-twenty-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivisibleByTwentyFour.DivisibleByTwentyFour

theorem divisible_by_twenty_four (n : ℤ) (hH1 : 0 ≤ n) :
    (24 : ℤ) ∣ (5 ^ (2 * n).toNat - 1 : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (24 : ℤ) ∣ (5 ^ (2 * m).toNat - 1 : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (5 ^ (2 * 0) - 1 : ℤ) = 24 * 0 := by parley_arith
      -- 1.2. def:divides d := 24, n := 5^(2·0) − 1, from 1.1
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (24 : ℤ)) (n := (5 ^ (2 * 0) - 1 : ℤ)))).mpr ⟨(0 : ℤ), s1_1⟩
    | succ m hK hIH =>
      -- 1.3. algebra
      have s1_3 : 2 * (m + 1) = 2 * m + 2 := by parley_ring
      -- 1.4. calculation
      have s1_4 : (5 ^ (2 * (m + 1)).toNat : ℤ) = 5 ^ (2 * m).toNat * 5 ^ 2 := by
        calc (5 ^ (2 * (m + 1)).toNat : ℤ) = 5 ^ (2 * m + 2).toNat := by parley_subst s1_3
          _ = 5 ^ (2 * m).toNat * 5 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (5 : ℤ)) (m := 2 * m) (by parley_side) (n := (2 : ℤ)) (by parley_side)); parley_side)
      -- 1.5. mun:divides-multiple e := 24, a := 5^(2m) − 1, x := 25, from IH
      have s1_5 : (24 : ℤ) ∣ ((5 ^ (2 * m).toNat - 1) * 25 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (24 : ℤ)) (a := (5 ^ (2 * m).toNat - 1 : ℤ)) (x := (25 : ℤ)) hIH)
      -- 1.6. mun:divides-self n := 24
      have s1_6 : (24 : ℤ) ∣ (24 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (24 : ℤ)))
      -- 1.7. mun:divides-sum d := 24, a := (5^(2m) − 1)·25, b := 24, from 1.5, 1.6
      have s1_7 : (24 : ℤ) ∣ ((5 ^ (2 * m).toNat - 1) * 25 + 24 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (24 : ℤ)) (a := ((5 ^ (2 * m).toNat - 1) * 25 : ℤ)) (b := (24 : ℤ)) s1_5 s1_6)
      -- 1.8. substitute
      have c1 : ((5 ^ (2 * m).toNat - 1) * 25 + 24 : ℤ) = 5 ^ (2 * (m + 1)).toNat - 1 := by linear_combination (norm := parley_norm) (-1) * s1_4
      have row1 : (24 : ℤ) ∣ (5 ^ (2 * (m + 1)).toNat - 1 : ℤ) := by parley_subst_at c1 s1_7
      exact row1
  -- 2. instantiate m := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.DivisibleByTwentyFour.DivisibleByTwentyFour
