module

public import AlgebraTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/modulus-plus-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder

theorem modulus_plus_remainder (A : ℤ) (hH1 : 0 ≤ A) (M : ℤ) (hH2 : 0 < M) (hH3 : A < M) :
    (M + A) % M = A := by
  -- 1. algebra
  have s1 : 1 * M + A = M + A := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * M + A = M + A := ⟨(1 : ℤ), s1⟩
  -- 3. mun:mod-remainder a := M + A, m := M, r := A, from H3, 2
  exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := M + A) (m := M) hH2 (r := A) hH1 hH3)).mpr s2

end Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder
