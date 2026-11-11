module

public import AlgebraTactics
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

/-! Written from proofs/hammack/gcd-minus-second-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural

theorem gcd_minus_second_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    (Int.gcd a b : ℤ) = (Int.gcd (a - b) b : ℤ) := by
  -- 1. mun:mod-multiple r := a, m := b, q := −1
  have s1 : (-1 * b + a) % b = a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) hH2 (q := (-1 : ℤ)))
  -- 2. substitute
  have s2 : (a - b) % b = a % b := by
    have c1 : -1 * b + a = a - b := by parley_ring
    have row1 : (a - b) % b = a % b := by (have h := Eq.subst (motive := (fun t : ℤ => t % b = a % b)) c1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 3. calculation
  calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) hH2).symm
    _ = (Int.gcd ((a - b) % b) b : ℤ) := by (have h := congrArg (fun t : ℤ => (Int.gcd t b : ℤ)) s2.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (Int.gcd (a - b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - b) (b := b) hH2)

end Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural
