module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/divisible-by-nine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivisibleByNine.DivisibleByNine

theorem divisible_by_nine (n : ℤ) (hH1 : 0 ≤ n) :
    (9 : ℤ) ∣ (4 ^ (3 * n).toNat + 8 : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (9 : ℤ) ∣ (4 ^ (3 * m).toNat + 8 : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (4 ^ (3 * 0) + 8 : ℤ) = 9 * 1 := by parley_arith
      -- 1.2. def:divides d := 9, n := 4^(3·0) + 8, from 1.1
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (9 : ℤ)) (n := (4 ^ (3 * 0) + 8 : ℤ)))).mpr ⟨(1 : ℤ), s1_1⟩
    | succ m hK hIH =>
      -- 1.3. algebra
      have s1_3 : 3 * (m + 1) = 3 * m + 3 := by parley_ring
      -- 1.4. calculation
      have s1_4 : (4 ^ (3 * (m + 1)).toNat : ℤ) = 4 ^ (3 * m).toNat * 4 ^ 3 := by
        calc (4 ^ (3 * (m + 1)).toNat : ℤ) = 4 ^ (3 * m + 3).toNat := by (have h := congrArg (fun t : ℤ => 4 ^ t.toNat) s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 4 ^ (3 * m).toNat * 4 ^ 3 := by
              have hI : (4 ^ (3 * m + 3).toNat : ℤ) = 4 ^ (3 * m).toNat * 4 ^ 3 := by parley_instance ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (4 : ℤ)) (m := 3 * m) (by parley_side) (n := (3 : ℤ)) (by parley_side)))
              exact hI
      -- 1.5. mun:divides-multiple e := 9, a := 4^(3m) + 8, x := 64, from IH
      have s1_5 : (9 : ℤ) ∣ ((4 ^ (3 * m).toNat + 8) * 64 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (9 : ℤ)) (a := (4 ^ (3 * m).toNat + 8 : ℤ)) (x := (64 : ℤ)) hIH)
      -- 1.6. def:divides d := 9, n := 504
      have r37_1 : (504 : ℤ) = 9 * 56 := by parley_arith
      have s1_6 : (9 : ℤ) ∣ (504 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (9 : ℤ)) (n := (504 : ℤ)))).mpr ⟨(56 : ℤ), by parley_side⟩
      -- 1.7. mun:divides-difference d := 9, a := (4^(3m) + 8)·64, b := 504, from 1.5, 1.6
      have s1_7 : (9 : ℤ) ∣ ((4 ^ (3 * m).toNat + 8) * 64 - 504 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (9 : ℤ)) (a := ((4 ^ (3 * m).toNat + 8) * 64 : ℤ)) (b := (504 : ℤ)) s1_5 s1_6)
      -- 1.8. substitute
      have c1 : ((4 ^ (3 * m).toNat + 8) * 64 - 504 : ℤ) = 4 ^ (3 * (m + 1)).toNat + 8 := by linear_combination (norm := parley_norm) (-1) * s1_4
      have row1 : (9 : ℤ) ∣ (4 ^ (3 * (m + 1)).toNat + 8 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (9 : ℤ) ∣ t)) c1 s1_7; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
  -- 2. instantiate m := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.DivisibleByNine.DivisibleByNine
