module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/hammack/sqrt6-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational

theorem sqrt6_irrational :
    Irrational (Real.sqrt (6 : ℝ)) := by
  -- 1. def:sqrt x := 6
  have r14_1 : (6 : ℤ) ≥ 0 := by parley_arith
  have s1 : Real.sqrt (6 : ℝ) ^ 2 = 6 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ) := by parley_suppose hc_hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √6, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (6 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √6 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 6 := by parley_subst_at s2_1b s1
    -- 2.3. algebra, from 2.2
    have r29_1 : q ≠ 0 := by parley_side
    have s2_3 : p ^ 2 = 6 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. algebra, from 2.3
    have s2_4 : p ^ 2 = 2 * (3 * q ^ 2) := by linear_combination (norm := parley_norm) s2_3
    -- 2.5. def:even n := p², from 2.4
    have s2_5 : Even (p ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨3 * q ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨3 * q ^ 2, by parley_side⟩; parley_side)
    -- 2.6. thm:even-square n := p, from 2.5
    have s2_6 : Even p := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5)).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5); parley_side)
    -- 2.7. obtain r: def:even n := p, from 2.6
    obtain ⟨r, s2_7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp (by parley_side)
    -- 2.8. substitute p = 2r (line 2.7) into line 2.3
    have s2_8 : (2 * r) ^ 2 = 6 * q ^ 2 := by parley_subst_at s2_7 s2_3
    -- 2.9. algebra, from 2.8
    have s2_9 : 2 * r ^ 2 = 3 * q ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s2_8
    -- 2.10. algebra, from 2.9
    have s2_10 : q ^ 2 = 2 * (r ^ 2 - q ^ 2) := by linear_combination (norm := parley_norm) (-1) * s2_9
    -- 2.11. def:even n := q², from 2.10
    have s2_11 : Even (q ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2 - q ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2 - q ^ 2, by parley_side⟩; parley_side)
    -- 2.12. thm:even-square n := q, from 2.11
    have s2_12 : Even q := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11)).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11); parley_side)
    -- 2.13. obtain s: def:even n := q, from 2.12
    obtain ⟨s, s2_13⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp (by parley_side)
    -- 2.14. def:divides d := 2, n := p, from 2.7
    have s2_14 : (2 : ℤ) ∣ p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩; parley_side)
    -- 2.15. def:divides d := 2, n := q, from 2.13
    have s2_15 : (2 : ℤ) ∣ q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩; parley_side)
    -- 2.16. exhibit, from 2.14, 2.15
    have r69_1 : (2 : ℤ) > 1 := by parley_arith
    have s2_16 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
    all_goals parley_side
  -- 3. def:irrational x := √6, from 2
  have s3 : Irrational (Real.sqrt (6 : ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (6 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (6 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational
