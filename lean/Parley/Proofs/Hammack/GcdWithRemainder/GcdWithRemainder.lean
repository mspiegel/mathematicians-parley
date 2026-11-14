module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/gcd-with-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

theorem gcd_with_remainder (a : ℤ) (b : ℤ) (hH2 : 0 < b) (q : ℤ) (r : ℤ) (hH5 : a = q * b + r) :
    (Int.gcd a b : ℤ) = (Int.gcd r b : ℤ) := by
  -- 1. calculation
  have s1 : a % b = r % b := by
    calc a % b = (q * b + r) % b := congrArg (fun t : ℤ => t % b) hH5
      _ = r % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := r) (m := b) hH2 (q := q))
  -- 2. calculation
  calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) hH2).symm
    _ = (Int.gcd (r % b) b : ℤ) := congrArg (fun t : ℤ => (Int.gcd t b : ℤ)) s1
    _ = (Int.gcd r b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := r) (b := b) hH2)

end Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder
