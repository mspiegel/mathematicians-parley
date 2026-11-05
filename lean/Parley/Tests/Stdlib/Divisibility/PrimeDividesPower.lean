module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.PrimeDividesPower

theorem prime_divides_power (q : ℕ) (hH1 : 0 < q) (hH2 : Nat.Prime q) (x : ℤ) (k : ℕ) (hH4 : 0 < k) :
    ((q : ℤ) ∣ x ^ k ↔ (q : ℤ) ∣ x) := by
  -- 1. thm:divisibility-prime-divides-power p := q, a := x, n := k, from H2
  have s1 : (q : ℤ) ∣ x ^ k ↔ (q : ℤ) ∣ x := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) (by parley_side) (a := x) (n := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) (by parley_side) (a := x) (n := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) (by parley_side) (a := x) (n := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) (by parley_side) (a := x) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) (by parley_side) (a := x) (n := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.PrimeDividesPower
