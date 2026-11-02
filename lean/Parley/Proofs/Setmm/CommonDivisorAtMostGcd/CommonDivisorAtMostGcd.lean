module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/common-divisor-at-most-gcd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.CommonDivisorAtMostGcd.CommonDivisorAtMostGcd

theorem common_divisor_at_most_gcd (K : ℕ) (hH1 : 0 < K) (M : ℕ) (hH2 : 0 < M) (N : ℕ) (hH3 : 0 < N) (hH4 : (K : ℤ) ∣ (M : ℤ)) (hH5 : (K : ℤ) ∣ (N : ℤ)) :
    (K : ℤ) ≤ (Int.gcd (M : ℤ) (N : ℤ) : ℤ) := by
  -- 1. thm:divides-gcd d := K, a := M, b := N, from H4, H5
  have s1 : (K : ℤ) ∣ (Int.gcd (M : ℤ) (N : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (K : ℤ)) (a := (M : ℤ)) (b := (N : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 2. def:gcd a := M, b := N
  have s2 : 0 < (Int.gcd (M : ℤ) (N : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)); parley_side)
  -- 3. mun:divides-le e := K, m := gcd(M, N), from 1, 2
  have s3 : (K : ℤ) ≤ (Int.gcd (M : ℤ) (N : ℤ) : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := Int.gcd (M : ℤ) (N : ℤ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := Int.gcd (M : ℤ) (N : ℤ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := Int.gcd (M : ℤ) (N : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := Int.gcd (M : ℤ) (N : ℤ)) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.CommonDivisorAtMostGcd.CommonDivisorAtMostGcd
