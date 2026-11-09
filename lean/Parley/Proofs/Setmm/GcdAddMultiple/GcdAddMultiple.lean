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

/-! Written from proofs/setmm/gcd-add-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GcdAddMultiple.GcdAddMultiple

theorem gcd_add_multiple (K : ℤ) (M : ℤ) (hH2 : 0 < M) (N : ℤ) :
    (Int.gcd M N : ℤ) = (Int.gcd M (N + K * M) : ℤ) := by
  -- 1. thm:gcd-mod a := N + K·M, b := M
  have s1 : (Int.gcd ((N + K * M) % M) M : ℤ) = (Int.gcd (N + K * M) M : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N + K * M) (b := M) (by parley_side))
  -- 2. mun:mod-multiple r := N, m := M, q := K
  have s2 : (K * M + N) % M = N % M := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := N) (m := M) (by parley_side) (q := K))
  -- 3. substitute
  have s3 : (N + K * M) % M = N % M := by
    have c1 : K * M + N = N + K * M := by parley_ring
    have row1 : (N + K * M) % M = N % M := by parley_subst_at c1 s2
    exact row1
  -- 4. substitute (N + K·M) mod M = N mod M (line 3) into line 1
  have s4 : (Int.gcd (N % M) M : ℤ) = (Int.gcd (N + K * M) M : ℤ) := by parley_subst_at s3 s1
  -- 5. calculation
  calc (Int.gcd M N : ℤ) = (Int.gcd N M : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N) (b := M)).symm
    _ = (Int.gcd (N % M) M : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := N) (b := M) (by parley_side)).symm
    _ = (Int.gcd (N + K * M) M : ℤ) := by exact s4
    _ = (Int.gcd M (N + K * M) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := N + K * M) (b := M))

end Parley.Proofs.Setmm.GcdAddMultiple.GcdAddMultiple
