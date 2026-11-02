module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/odd-prime-above-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddPrimeAboveTwo.OddPrimeAboveTwo

theorem odd_prime_above_two (P : ℕ) (hH1 : 0 < P) (hH2 : Nat.Prime P) (hH3 : (P : ℤ) ≠ 2) :
    2 < (P : ℤ) := by
  -- 1. def:prime p := P, from H2
  have s1 : (P : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. mun:integer-step m := 1, n := P, from 1
  have s2 : 1 + 1 ≤ (P : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (P : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (P : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (P : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := (P : ℤ)) (by parley_side)); parley_side)
  -- 3. inequalities, from H3, 2
  have s3 : 2 < (P : ℤ) := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.OddPrimeAboveTwo.OddPrimeAboveTwo
