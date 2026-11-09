module

public import AlgebraTactics
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

/-! Written from proofs/hammack/gcd-minus-second-natural.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural

theorem gcd_minus_second_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    (Int.gcd a b : ℤ) = (Int.gcd (a - b) b : ℤ) := by
  -- 1. mun:mod-multiple r := a, m := b, q := −1
  have s1 : (-1 * b + a) % b = a % b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := a) (m := b) (by parley_side) (q := (-1 : ℤ)))
  -- 2. substitute
  have s2 : (a - b) % b = a % b := by
    have c1 : -1 * b + a = a - b := by parley_ring
    have row1 : (a - b) % b = a % b := by parley_subst_at c1 s1
    exact row1
  -- 3. calculation
  calc (Int.gcd a b : ℤ) = (Int.gcd (a % b) b : ℤ) := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)).symm
    _ = (Int.gcd ((a - b) % b) b : ℤ) := by parley_subst s2
    _ = (Int.gcd (a - b) b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a - b) (b := b) (by parley_side))

end Parley.Proofs.Hammack.GcdMinusSecondNatural.GcdMinusSecondNatural
