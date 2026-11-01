module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Library
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg

theorem even_leg (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (hH4 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2) :
    (Even (a : ℤ) ∨ Even (b : ℤ)) := by
  -- 1. mun:even-or-odd n := a
  have s1 : Even (a : ℤ) ∨ Odd (a : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (a : ℤ)))
  -- 2. cases, from 1
  have s2 : Even (a : ℤ) ∨ Even (b : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:or-left, from C1
      have s2_1 : Even (a : ℤ) ∨ Even (b : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side))
      all_goals parley_side
    · skip
      -- 2.2. contradiction
      have s2_2 : ¬ Odd (b : ℤ) := by
        by_contra hc_hS
        have hS : Odd (b : ℤ) := by parley_suppose hc_hS
        -- 2.2.1. obtain p: def:odd n := a, from C2
        obtain ⟨p, s2_2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (a : ℤ)))).mp (by parley_side)
        -- 2.2.2. obtain q: def:odd n := b, from S
        obtain ⟨q, s2_2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (b : ℤ)))).mp (by parley_side)
        -- 2.2.3. substitute
        have s2_2_3 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = (c : ℤ) ^ 2 := by
          have c1 : (a : ℤ) = 2 * p + 1 := by parley_subst s2_2_1
          have row1 : (2 * p + 1) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by parley_subst_at c1 hH4
          have c2 : (b : ℤ) = 2 * q + 1 := by parley_subst s2_2_2
          have row2 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = (c : ℤ) ^ 2 := by parley_subst_at c2 row1
          exact row2
        -- 2.2.4. calculation
        have s2_2_4 : (c : ℤ) ^ 2 = 2 * (2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1) := by
          calc (c : ℤ) ^ 2 = (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 := by parley_side
            _ = 2 * (2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1) := by ring
        -- 2.2.5. def:even n := c², from 2.2.4
        have s2_2_5 : Even ((c : ℤ) ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) ^ 2))).mpr ⟨2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1, by parley_side⟩
        -- 2.2.6. thm:even-square n := c, from 2.2.5
        have s2_2_6 : Even (c : ℤ) := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := (c : ℤ)) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := (c : ℤ)) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := (c : ℤ)) (by parley_side))
        -- 2.2.7. obtain r: def:even n := c, from 2.2.6
        obtain ⟨r, s2_2_7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ)))).mp (by parley_side)
        -- 2.2.8. substitute c = 2r (line 2.2.7) into line 2.2.3
        have s2_2_8 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = (2 * r) ^ 2 := by parley_subst_at s2_2_7 s2_2_3
        -- 2.2.9. algebra, from 2.2.8
        have s2_2_9 : 2 = 4 * (r ^ 2 - p ^ 2 - p - q ^ 2 - q) := by linear_combination s2_2_8
        -- 2.2.10. def:divides d := 4, n := 2, from 2.2.9
        have s2_2_10 : (4 : ℤ) ∣ (2 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (2 : ℤ)))).mpr ⟨r ^ 2 - p ^ 2 - p - q ^ 2 - q, by parley_side⟩
        exact absurd s2_2_10 (by norm_num)
        all_goals parley_side
      -- 2.3. mun:even-or-odd n := b
      have s2_3 : Even (b : ℤ) ∨ Odd (b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ)))
      -- 2.4. mun:disjunctive-syllogism P := b is even, Q := b is odd, from 2.2, 2.3
      have s2_4 : Even (b : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) (by parley_side) (by parley_side))
      -- 2.5. mun:or-right, from 2.4
      have s2_5 : Even (a : ℤ) ∨ Even (b : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even (a : ℤ)) (Q := Even (b : ℤ)) (by parley_side))
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Wiedijk.PythagoreanTriples.EvenLeg
