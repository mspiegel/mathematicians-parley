module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.PrimeDividesPower

theorem prime_divides_power (q : ℤ) (hH1 : 0 < q) (hH2 : Nat.Prime q.toNat) (x : ℤ) (k : ℤ) (hH4 : 0 < k) :
    (q ∣ x ^ k.toNat ↔ q ∣ x) := by
  -- 1. thm:divisibility-prime-divides-power p := q, a := x, n := k, from H2
  have s1 : q ∣ x ^ k.toNat ↔ q ∣ x := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.PrimeDividesPower
