module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-times-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalTimesIrrational.RationalTimesIrrational

theorem rational_times_irrational (a : ℝ) (b : ℝ) (a : ℚ) (hH4 : Irrational ((a : ℝ) * b)) :
    Irrational b := by
  -- 1. contradiction
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = b) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = b := by parley_suppose hc_hS
    -- 1.1. obtain p, q: def:rational x := a, from H3
    obtain ⟨p, q, s1_1a, s1_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := a))).mp (by parley_side)
    -- 1.2. obtain r, s: def:rational x := b, from S
    obtain ⟨r, s, s1_2a, s1_2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := b))).mp (by parley_side)
    -- 1.3. calculation
    have s1_3 : (a : ℝ) * b = (p : ℝ) * (r : ℝ) / ((q : ℝ) * (s : ℝ)) := by
      calc (a : ℝ) * b = (p : ℝ) / (q : ℝ) * b := by
            have s1_1b_w : (a : ℝ) = (p : ℝ) / (q : ℝ) := by have h := congrArg (fun x : ℚ => (x : ℝ)) s1_1b; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s1_1b_w | parley_subst s1_1b
        _ = (p : ℝ) / (q : ℝ) * ((r : ℝ) / (s : ℝ)) := by parley_subst s1_2b
        _ = (p : ℝ) * (r : ℝ) / ((q : ℝ) * (s : ℝ)) := by parley_ring
    -- 1.4. def:rational x := a·b, from 1.3
    have s1_4 : ∃ m : ℚ, (m : ℝ) = (a : ℝ) * b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := (a : ℝ) * b))).mpr ⟨p * r, q * s, by parley_side, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := (a : ℝ) * b))).mpr ⟨p * r, q * s, by parley_side, by parley_side⟩; parley_side)
    -- 1.5. def:irrational x := a·b, from H4
    have s1_5 : ¬ (∃ m : ℚ, (m : ℝ) = (a : ℝ) * b) := by first | exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := (a : ℝ) * b))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Numbers.def_irrational (x := (a : ℝ) * b))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Numbers.def_irrational (x := (a : ℝ) * b))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Numbers.def_irrational (x := (a : ℝ) * b))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.def_irrational (x := (a : ℝ) * b))).mp (by parley_side)).2; parley_side)
    -- 1.6. restate 1.5
    have s1_6 : ¬ (∃ m : ℚ, (m : ℝ) = (a : ℝ) * b) := by parley_side
    all_goals parley_side
  -- 2. def:irrational x := b, from 1
  have s2 : Irrational b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := b))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := b))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.RationalTimesIrrational.RationalTimesIrrational
