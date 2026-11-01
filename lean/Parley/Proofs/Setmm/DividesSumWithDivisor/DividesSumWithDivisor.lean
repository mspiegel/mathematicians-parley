module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/divides-sum-with-divisor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DividesSumWithDivisor.DividesSumWithDivisor

theorem divides_sum_with_divisor (M : ℤ) (N : ℤ) :
    (M ∣ N ↔ M ∣ M + N) := by
  -- the theorem. both directions
  have sThm : M ∣ N ↔ M ∣ M + N := by
    constructor
    · skip
      intro hD1
      -- 1. mun:divides-self n := M
      have s1 : M ∣ M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))
      -- 2. mun:divides-sum d := M, a := M, b := N, from D1, 1
      have s2 : M ∣ M + N := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := M) (a := M) (b := N) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := M) (a := M) (b := N) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := M) (a := M) (b := N) (by parley_side) (by parley_side))
      all_goals parley_side
    · skip
      intro hD2
      -- 3. mun:divides-self n := M
      have s3 : M ∣ M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := M))
      -- 4. mun:divides-difference d := M, a := M + N, b := M, from D2, 3
      have s4 : M ∣ M + N - M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := M) (a := M + N) (b := M) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := M) (a := M + N) (b := M) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := M) (a := M + N) (b := M) (by parley_side) (by parley_side))
      -- 5. substitute
      have s5 : M ∣ N := by
        have c1 : M + N - M = N := by ring
        have row1 : M ∣ N := by parley_subst_at c1 s4
        exact row1
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.DividesSumWithDivisor.DividesSumWithDivisor
