module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.FourHasAPrimeFactor

theorem four_has_a_prime_factor :
    (∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) ∣ (4 : ℤ))) := by
  -- 1. thm:prime-factor m := 4
  have r36_1 : (4 : ℤ) > 1 := by parley_arith
  have s1 : ∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) ∣ (4 : ℤ)) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := 4) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := 4) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := 4) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := 4) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := 4) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Docs.Grammar.FourHasAPrimeFactor
