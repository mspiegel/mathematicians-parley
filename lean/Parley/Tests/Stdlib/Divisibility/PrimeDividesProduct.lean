module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.PrimeDividesProduct

theorem prime_divides_product (p : ℕ) (hH1 : 0 < p) (hH2 : Nat.Prime p) (m : ℤ) (n : ℤ) :
    ((p : ℤ) ∣ m * n ↔ (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n) := by
  -- 1. thm:divisibility-prime-divides-product, from H2
  have s1 : (p : ℤ) ∣ m * n ↔ (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) (by parley_side) (m := m) (n := n)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.PrimeDividesProduct
