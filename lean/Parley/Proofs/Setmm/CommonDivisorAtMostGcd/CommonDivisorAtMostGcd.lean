module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
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
  have s1 : K ∣ (Int.gcd M N : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := K) (a := M) (b := N) hH4 hH5)
  -- 2. def:gcd a := M, b := N
  have s2 : 0 < (Int.gcd M N : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := M) hH2 (b := N) hH3)
  -- 3. mun:divides-le e := K, m := gcd(M, N), from 1, 2
  exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := K) hH1 (m := (Int.gcd M N : ℤ)) s2 s1)

end Parley.Proofs.Setmm.CommonDivisorAtMostGcd.CommonDivisorAtMostGcd
