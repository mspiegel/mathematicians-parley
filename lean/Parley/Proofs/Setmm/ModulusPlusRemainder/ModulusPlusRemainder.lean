module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/modulus-plus-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder

theorem modulus_plus_remainder (A : ℤ) (hH1 : 0 ≤ A) (M : ℤ) (hH2 : 0 < M) (hH3 : A < M) :
    (M + A) % M = A := by
  -- 1. algebra
  have s1 : 1 * M + A = M + A := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * M + A = M + A := ⟨(1 : ℤ), by parley_side⟩
  -- 3. mun:mod-remainder a := M + A, m := M, r := A, from H3, 2
  have s3 : (M + A) % M = A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := M + A) (m := M) (by parley_side) (r := A) (by parley_side) hH3)).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := M + A) (m := M) (by parley_side) (r := A) (by parley_side) hH3)).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder
