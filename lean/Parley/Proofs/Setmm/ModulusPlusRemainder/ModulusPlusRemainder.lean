module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/modulus-plus-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder

theorem modulus_plus_remainder (A : ℕ) (M : ℕ) (hH2 : 0 < M) (hH3 : (A : ℤ) < (M : ℤ)) :
    ((M : ℤ) + (A : ℤ)) % (M : ℤ) = (A : ℤ) := by
  -- 1. algebra
  have s1 : 1 * (M : ℤ) + (A : ℤ) = (M : ℤ) + (A : ℤ) := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * (M : ℤ) + (A : ℤ) = (M : ℤ) + (A : ℤ) := ⟨(1 : ℤ), by parley_side⟩
  -- 3. mun:mod-remainder a := M + A, m := M, r := A, from H3, 2
  have s3 : ((M : ℤ) + (A : ℤ)) % (M : ℤ) = (A : ℤ) := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (M : ℤ) + (A : ℤ)) (m := M) (by parley_side) (r := A) (by parley_side))).mpr (by parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.ModulusPlusRemainder.ModulusPlusRemainder
