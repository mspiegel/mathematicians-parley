module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.Bezout.Bezout

/-! Written from proofs/hammack/coprime-to-a-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CoprimeToAProduct.CoprimeToAProduct

theorem coprime_to_a_product (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (hH4 : (Int.gcd (a : ℤ) (c : ℤ) : ℤ) = 1) (hH5 : (Int.gcd (b : ℤ) (c : ℤ) : ℤ) = 1) :
    (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) = 1 := by
  -- 1. obtain x, y: thm:bezout b := c
  obtain ⟨x, y, s1⟩ := (Parley.Proofs.Wiedijk.Bezout.Bezout.bezout (a := a) (by parley_side) (b := c) (by parley_side))
  -- 2. substitute gcd(a, c) = 1 (H4) into line 1
  have s2 : (a : ℤ) * x + (c : ℤ) * y = 1 := by parley_subst_at hH4 s1
  -- 3. obtain u, v: thm:bezout a := b, b := c
  obtain ⟨u, v, s3⟩ := (Parley.Proofs.Wiedijk.Bezout.Bezout.bezout (a := b) (by parley_side) (b := c) (by parley_side))
  -- 4. substitute gcd(b, c) = 1 (H5) into line 3
  have s4 : (b : ℤ) * u + (c : ℤ) * v = 1 := by parley_subst_at hH5 s3
  -- 5. calculation
  have s5 : (a : ℤ) * (b : ℤ) * (x * u) + (c : ℤ) * ((a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) = 1 := by
    calc (a : ℤ) * (b : ℤ) * (x * u) + (c : ℤ) * ((a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) = ((a : ℤ) * x + (c : ℤ) * y) * ((b : ℤ) * u + (c : ℤ) * v) := by parley_ring
      _ = 1 * ((b : ℤ) * u + (c : ℤ) * v) := by parley_subst s2
      _ = 1 := by parley_side
  -- 6. def:gcd a := a·b, b := c
  have s6a : 0 < (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (by parley_side) (b := c) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (by parley_side) (b := c) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a * b) (by parley_side) (b := c) (by parley_side)); parley_side)
  have s6b : (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) ∣ (a : ℤ) * (b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (by parley_side) (b := c) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (by parley_side) (b := c) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a * b) (by parley_side) (b := c) (by parley_side)); parley_side)
  have s6c : (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) ∣ (c : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (by parley_side) (b := c) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (by parley_side) (b := c) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (by parley_side) (b := c) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a * b) (by parley_side) (b := c) (by parley_side)); parley_side)
  -- 7. mun:divides-combination e := gcd(a·b, c), a := a·b, b := c, x := x·u, y := a·x·v + y·b·u + c·y·v, from 6
  have s7 : (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) ∣ (a : ℤ) * (b : ℤ) * (x * u) + (c : ℤ) * ((a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ)) (a := (a : ℤ) * (b : ℤ)) (b := (c : ℤ)) (x := x * u) (y := (a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) s6b s6c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ)) (a := (a : ℤ) * (b : ℤ)) (b := (c : ℤ)) (x := x * u) (y := (a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) s6b s6c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ)) (a := (a : ℤ) * (b : ℤ)) (b := (c : ℤ)) (x := x * u) (y := (a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) s6b s6c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ)) (a := (a : ℤ) * (b : ℤ)) (b := (c : ℤ)) (x := x * u) (y := (a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) s6b s6c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ)) (a := (a : ℤ) * (b : ℤ)) (b := (c : ℤ)) (x := x * u) (y := (a : ℤ) * x * v + y * (b : ℤ) * u + (c : ℤ) * y * v) s6b s6c); parley_side)
  -- 8. substitute a·b·(x·u) + c·(a·x·v + y·b·u + c·y·v) = 1 (line 5) into line 7
  have s8 : (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) ∣ (1 : ℤ) := by parley_subst_at s5 s7
  -- 9. mun:divides-one d := gcd(a·b, c), from 6, 8
  have s9 : (Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd ((a : ℤ) * (b : ℤ)) (c : ℤ)) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s9

end Parley.Proofs.Hammack.CoprimeToAProduct.CoprimeToAProduct
