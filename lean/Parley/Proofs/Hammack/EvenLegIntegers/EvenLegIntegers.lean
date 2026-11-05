module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare

/-! Written from proofs/hammack/even-leg-integers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EvenLegIntegers.EvenLegIntegers

set_option maxHeartbeats 400000 in
theorem even_leg_integers (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) :
    (Even a ∨ Even b) := by
  -- 1. mun:even-or-odd n := a
  have s1 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); parley_side)
  -- 2. cases, from 1
  have s2 : Even a ∨ Even b := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:or-left, from C1
      have s2_1 : Even a ∨ Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even a) (Q := Even b) hC1); parley_side)
      all_goals parley_side
    · skip
      -- 2.2. contradiction
      have s2_2 : ¬ Odd b := by
        by_contra hc_hS
        have hS : Odd b := by parley_suppose hc_hS
        -- 2.2.1. obtain p: def:odd n := a, from C2
        obtain ⟨p, s2_2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
        -- 2.2.2. obtain q: def:odd n := b, from S
        obtain ⟨q, s2_2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp (by parley_side)
        -- 2.2.3. substitute
        have s2_2_3 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by
          have c1 : a = 2 * p + 1 := by parley_subst s2_2_1
          have row1 : (2 * p + 1) ^ 2 + b ^ 2 = c ^ 2 := by parley_subst_at c1 hH4
          have c2 : b = 2 * q + 1 := by parley_subst s2_2_2
          have row2 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by parley_subst_at c2 row1
          exact row2
        -- 2.2.4. algebra, from 2.2.3
        have s2_2_4 : c ^ 2 = 2 * (2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1) := by linear_combination (norm := parley_norm) (-1) * s2_2_3
        -- 2.2.5. def:even n := c², from 2.2.4
        have s2_2_5 : Even (c ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := c ^ 2))).mpr ⟨2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := c ^ 2))).mpr ⟨2 * p ^ 2 + 2 * p + 2 * q ^ 2 + 2 * q + 1, by parley_side⟩; parley_side)
        -- 2.2.6. thm:even-square n := c, from 2.2.5
        have s2_2_6 : Even c := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) s2_2_5) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) s2_2_5)).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) s2_2_5) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) s2_2_5) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := c) s2_2_5); parley_side)
        -- 2.2.7. obtain r: def:even n := c, from 2.2.6
        obtain ⟨r, s2_2_7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := c))).mp (by parley_side)
        -- 2.2.8. substitute c = 2r (line 2.2.7) into line 2.2.3
        have s2_2_8 : (2 * p + 1) ^ 2 + (2 * q + 1) ^ 2 = (2 * r) ^ 2 := by parley_subst_at s2_2_7 s2_2_3
        -- 2.2.9. algebra, from 2.2.8
        have s2_2_9 : 2 = 4 * (r ^ 2 - p ^ 2 - p - q ^ 2 - q) := by linear_combination (norm := parley_norm) s2_2_8
        -- 2.2.10. def:divides d := 4, n := 2, from 2.2.9
        have s2_2_10 : (4 : ℤ) ∣ (2 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (2 : ℤ)))).mpr ⟨r ^ 2 - p ^ 2 - p - q ^ 2 - q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := (2 : ℤ)))).mpr ⟨r ^ 2 - p ^ 2 - p - q ^ 2 - q, by parley_side⟩; parley_side)
        exact absurd s2_2_10 (by norm_num)
        all_goals parley_side
      -- 2.3. mun:even-or-odd n := b
      have s2_3 : Even b ∨ Odd b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)); parley_side)
      -- 2.4. mun:disjunctive-syllogism P := b is even, Q := b is odd, from 2.2, 2.3
      have s2_4 : Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s2_3 s2_2); parley_side)
      -- 2.5. mun:or-right, from 2.4
      have s2_5 : Even a ∨ Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even a) (Q := Even b) s2_4); parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.EvenLegIntegers.EvenLegIntegers
