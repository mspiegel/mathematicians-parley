module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare

/-! Written from proofs/hammack/square-minus-four-b-minus-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareMinusFourBMinusTwo.SquareMinusFourBMinusTwo

theorem square_minus_four_b_minus_two (a : ℤ) (b : ℤ) :
    a ^ 2 - 4 * b - 2 ≠ 0 := by
  -- the theorem. contradiction
  have sThm : a ^ 2 - 4 * b - 2 ≠ 0 := by
    by_contra hc_hS
    have hS : a ^ 2 - 4 * b - 2 = 0 := by parley_suppose hc_hS
    -- 1. algebra, from S
    have s1 : a ^ 2 = 4 * b + 2 := by linear_combination (norm := parley_norm) hS
    -- 2. algebra, from 1
    have s2 : a ^ 2 = 2 * (2 * b + 1) := by linear_combination (norm := parley_norm) s1
    -- 3. def:even n := a², from 2
    have s3 : Even (a ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2))).mpr ⟨2 * b + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2))).mpr ⟨2 * b + 1, by parley_side⟩; parley_side)
    -- 4. thm:even-square n := a, from 3
    have s4 : Even a := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side)); parley_side)
    -- 5. obtain k: def:even n := a, from 4
    obtain ⟨k, s5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
    -- 6. calculation
    have s6 : 4 * k ^ 2 = 4 * b + 2 := by
      calc 4 * k ^ 2 = (2 * k) ^ 2 := by parley_ring
        _ = a ^ 2 := by parley_subst s5
        _ = 4 * b + 2 := by parley_side
    -- 7. algebra, from 6
    have s7 : 1 = 2 * (k ^ 2 - b) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 2 : ℚ)) * s6
    -- 8. def:even n := 1, from 7
    have s8 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k ^ 2 - b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k ^ 2 - b, by parley_side⟩; parley_side)
    -- 9. mun:not-both n := 1, from 8
    have s9 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) (by parley_side)); parley_side)
    -- 10. arithmetic
    have s10 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquareMinusFourBMinusTwo.SquareMinusFourBMinusTwo
