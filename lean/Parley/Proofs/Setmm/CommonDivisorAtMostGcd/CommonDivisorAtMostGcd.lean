module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/common-divisor-at-most-gcd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.CommonDivisorAtMostGcd.CommonDivisorAtMostGcd

theorem common_divisor_at_most_gcd (K : ℤ) (hH1 : 0 < K) (M : ℤ) (hH2 : 0 < M) (N : ℤ) (hH3 : 0 < N) (hH4 : K ∣ M) (hH5 : K ∣ N) :
    K ≤ (Int.gcd M N : ℤ) := by
  -- 1. thm:divides-gcd d := K, a := M, b := N, from H4, H5
  have s1 : K ∣ (Int.gcd M N : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5); parley_side)
  -- 2. def:gcd a := M, b := N
  have s2 : 0 < (Int.gcd M N : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) (by parley_side) (b := N) (by parley_side)); parley_side)
  -- 3. mun:divides-le e := K, m := gcd(M, N), from 1, 2
  have s3 : K ≤ (Int.gcd M N : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := (Int.gcd M N : ℤ)) (by parley_side) s1)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := (Int.gcd M N : ℤ)) (by parley_side) s1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := (Int.gcd M N : ℤ)) (by parley_side) s1) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) (by parley_side) (m := (Int.gcd M N : ℤ)) (by parley_side) s1); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.CommonDivisorAtMostGcd.CommonDivisorAtMostGcd
