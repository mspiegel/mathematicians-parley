module

public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/gcd-with-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

theorem gcd_with_remainder (a : ℤ) (b : ℤ) (hH2 : 0 < b) (q : ℤ) (r : ℤ) (hH5 : a = q * b + r) :
    (Int.gcd a b : ℤ) = (Int.gcd r b : ℤ) := by
  -- 1. calculation
  have s1 : a % b = r % b := by
    calc a % b = (q * b + r) % b := by parley_subst hH5
      _ = r % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) (by parley_side) (q := q))
  -- 2. calculation
  calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)).symm
    _ = (Int.gcd (r % b) b : ℤ) := by parley_subst s1
    _ = (Int.gcd r b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) (by parley_side))

end Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder
