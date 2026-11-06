module

public import AlgebraTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural

/-! Written from proofs/hammack/gcd-with-successor-two-from-minus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GcdWithSuccessorTwoFromMinusOne.GcdWithSuccessorTwoFromMinusOne

set_option maxHeartbeats 400000 in
theorem gcd_with_successor_two_from_minus_one (n : ℤ) (hH2 : n ≥ -1) :
    (Int.gcd n (n + 2) : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by
  -- 1. mun:pos-int-nat m := n + 2
  have r19_1 : 0 < n + 2 := by parley_order
  have s1 : 0 < n + 2 := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n + 2) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n + 2) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n + 2) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n + 2) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n + 2) (by parley_set_side)); parley_set_side)
  -- 2. thm:gcd-integer-natural a := n, b := n + 2, from 1
  have s2a : 0 < (Int.gcd n (n + 2) : ℤ) := by first | exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).1 | exact ((Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).1).symm | simpa using (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).1 | exact_mod_cast (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).1 | (have h := (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).1; parley_set_side)
  have s2b : (Int.gcd n (n + 2) : ℤ) ∣ n := by first | exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.1 | exact ((Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.1).symm | simpa using (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.1 | exact_mod_cast (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.1 | (have h := (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.1; parley_set_side)
  have s2c : (Int.gcd n (n + 2) : ℤ) ∣ n + 2 := by first | exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.2 | exact ((Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.2).symm | simpa using (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.2 | exact_mod_cast (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.2 | (have h := (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := n) (b := n + 2) (by parley_set_side)).2.2; parley_set_side)
  -- 3. mun:divides-difference d := gcd(n, n + 2), a := n + 2, b := n, from 2
  have s3 : (Int.gcd n (n + 2) : ℤ) ∣ n + 2 - n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 2) : ℤ)) (a := n + 2) (b := n) s2c s2b) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 2) : ℤ)) (a := n + 2) (b := n) s2c s2b)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 2) : ℤ)) (a := n + 2) (b := n) s2c s2b) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 2) : ℤ)) (a := n + 2) (b := n) s2c s2b) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd n (n + 2) : ℤ)) (a := n + 2) (b := n) s2c s2b); parley_set_side)
  -- 4. substitute
  have s4 : (Int.gcd n (n + 2) : ℤ) ∣ (2 : ℤ) := by
    have c1 : n + 2 - n = 2 := by parley_ring
    have row1 : (Int.gcd n (n + 2) : ℤ) ∣ (2 : ℤ) := by parley_subst_at c1 s3
    exact row1
  -- 5. mun:divides-le e := gcd(n, n + 2), m := 2, from 2, 4
  have s5 : (Int.gcd n (n + 2) : ℤ) ≤ 2 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd n (n + 2) : ℤ)) (by parley_set_side) (m := (2 : ℤ)) (by parley_set_side) s4)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd n (n + 2) : ℤ)) (by parley_set_side) (m := (2 : ℤ)) (by parley_set_side) s4); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd n (n + 2) : ℤ)) (by parley_set_side) (m := (2 : ℤ)) (by parley_set_side) s4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd n (n + 2) : ℤ)) (by parley_set_side) (m := (2 : ℤ)) (by parley_set_side) s4); parley_set_side)
  -- 6. mun:le-cases x := gcd(n, n + 2), y := 2, from 5
  have s6 : (Int.gcd n (n + 2) : ℤ) < 2 ∨ (Int.gcd n (n + 2) : ℤ) = 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (Int.gcd n (n + 2) : ℤ)) (y := (2 : ℤ)))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (Int.gcd n (n + 2) : ℤ)) (y := (2 : ℤ)))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (Int.gcd n (n + 2) : ℤ)) (y := (2 : ℤ)))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (Int.gcd n (n + 2) : ℤ)) (y := (2 : ℤ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (Int.gcd n (n + 2) : ℤ)) (y := (2 : ℤ)))).mp (by parley_set_side); parley_set_side)
  -- 7. cases, from 6
  have s7 : (Int.gcd n (n + 2) : ℤ) = 1 ∨ (Int.gcd n (n + 2) : ℤ) = 2 := by
    rcases s6 with hC1 | hC2
    · skip
      -- 7.1. mun:integer-step m := gcd(n, n + 2), n := 2, from C1
      have s7_1 : (Int.gcd n (n + 2) : ℤ) + 1 ≤ 2 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (Int.gcd n (n + 2) : ℤ)) (n := (2 : ℤ)) hC1)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (Int.gcd n (n + 2) : ℤ)) (n := (2 : ℤ)) hC1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (Int.gcd n (n + 2) : ℤ)) (n := (2 : ℤ)) hC1) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (Int.gcd n (n + 2) : ℤ)) (n := (2 : ℤ)) hC1); parley_set_side)
      -- 7.2. inequalities, from 7.1
      have s7_2 : (Int.gcd n (n + 2) : ℤ) ≤ 1 := by parley_order
      -- 7.3. inequalities, from 2
      have s7_3 : 1 ≤ (Int.gcd n (n + 2) : ℤ) := by parley_order
      -- 7.4. antisymmetry, from 7.2, 7.3
      have s7_4 : (Int.gcd n (n + 2) : ℤ) = 1 := by parley_set_side
      -- 7.5. mun:or-left, from 7.4
      have s7_5 : (Int.gcd n (n + 2) : ℤ) = 1 ∨ (Int.gcd n (n + 2) : ℤ) = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) s7_4) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) s7_4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) s7_4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) s7_4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) s7_4); parley_set_side)
      all_goals parley_set_side
    · skip
      -- 7.6. mun:or-right, from C2
      have s7_6 : (Int.gcd n (n + 2) : ℤ) = 1 ∨ (Int.gcd n (n + 2) : ℤ) = 2 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) hC2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) hC2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) hC2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) hC2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (Int.gcd n (n + 2) : ℤ) = 1) (Q := (Int.gcd n (n + 2) : ℤ) = 2) hC2); parley_set_side)
      all_goals parley_set_side
  -- 8. def:pair x := gcd(n, n + 2), u := 1, w := 2, from 7
  have s8 : (Int.gcd n (n + 2) : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (Int.gcd n (n + 2) : ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (Int.gcd n (n + 2) : ℤ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s8

end Parley.Proofs.Hammack.GcdWithSuccessorTwoFromMinusOne.GcdWithSuccessorTwoFromMinusOne
