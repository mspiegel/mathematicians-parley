module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/divides-difference-with-divisor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DividesDifferenceWithDivisor.DividesDifferenceWithDivisor

theorem divides_difference_with_divisor (M : ℤ) (N : ℤ) :
    (M ∣ N ↔ M ∣ M - N) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. mun:divides-self n := M
    have s1 : M ∣ M := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))
    -- 2. mun:divides-difference d := M, a := M, b := N, from D1, 1
    exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := M) (a := M) (b := N) s1 hD1)
  · skip
    intro hD2
    -- 3. mun:divides-self n := M
    have s3 : M ∣ M := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))
    -- 4. mun:divides-difference d := M, a := M, b := M − N, from D2, 3
    have s4 : M ∣ M - (M - N) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := M) (a := M) (b := M - N) s3 hD2)
    -- 5. substitute
    have c1 : M - (M - N) = N := by parley_ring
    have row1 : M ∣ N := by parley_subst_at c1 s4
    exact row1

end Parley.Proofs.Setmm.DividesDifferenceWithDivisor.DividesDifferenceWithDivisor
