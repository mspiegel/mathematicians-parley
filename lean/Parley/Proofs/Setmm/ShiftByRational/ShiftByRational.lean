module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/shift-by-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ShiftByRational.ShiftByRational

theorem shift_by_rational (A : ℂ) (B : ℚ) :
    (True ∧ (∃ m : ℚ, (m : ℂ) = A + (B : ℂ)) ↔ (∃ m : ℚ, (m : ℂ) = A)) := by
  -- 1. obtain r, s: def:rational x := B
  obtain ⟨r, s, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp (by parley_side)
  -- 2. both directions
  have s2 : True ∧ (∃ m : ℚ, (m : ℂ) = A + (B : ℂ)) ↔ (∃ m : ℚ, (m : ℂ) = A) := by
    constructor
    · skip
      intro hD1
      -- 2.1. obtain p, q: def:rational x := A + B, from D1
      obtain ⟨p, q, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A + (B : ℂ)))).mp (by parley_side)
      -- 2.2. calculation
      have s2_2 : A = ((p : ℂ) * (s : ℂ) - (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by
        calc A = (p : ℂ) / (q : ℂ) - (B : ℂ) := by linear_combination (norm := parley_field) s2_1b
          _ = (p : ℂ) / (q : ℂ) - (r : ℂ) / (s : ℂ) := by
              have s1b_w : (B : ℂ) = (r : ℂ) / (s : ℂ) := by have h := congrArg (fun x : ℚ => (x : ℂ)) s1b; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s1b_w | parley_subst s1b
          _ = ((p : ℂ) * (s : ℂ) - (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by parley_ring
      -- 2.3. def:rational x := A, from 2.2
      have s2_3 : ∃ m : ℚ, (m : ℂ) = A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mpr ⟨p * s - r * q, q * s, by parley_side, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mpr ⟨p * s - r * q, q * s, by parley_side, by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 2.4. obtain p, q: def:rational x := A, from D2
      obtain ⟨p, q, s2_4a, s2_4b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
      -- 2.5. membership, from D2
      -- 2.6. calculation
      have s2_6 : A + (B : ℂ) = ((p : ℂ) * (s : ℂ) + (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by
        calc A + (B : ℂ) = (p : ℂ) / (q : ℂ) + (B : ℂ) := by parley_subst s2_4b
          _ = (p : ℂ) / (q : ℂ) + (r : ℂ) / (s : ℂ) := by
              have s1b_w : (B : ℂ) = (r : ℂ) / (s : ℂ) := by have h := congrArg (fun x : ℚ => (x : ℂ)) s1b; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s1b_w | parley_subst s1b
          _ = ((p : ℂ) * (s : ℂ) + (r : ℂ) * (q : ℂ)) / ((q : ℂ) * (s : ℂ)) := by parley_ring
      -- 2.7. def:rational x := A + B, from 2.6
      have s2_7 : ∃ m : ℚ, (m : ℂ) = A + (B : ℂ) := by (exact ⟨(Classical.choose hD2 : ℚ) + B, by push_cast; (try simp only [Classical.choose_spec hD2]); first | done | parley_ring⟩)
      -- 2.8. join 2.5, 2.7
      have s2_8 : True ∧ (∃ m : ℚ, (m : ℂ) = A + (B : ℂ)) := by parley_side
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.ShiftByRational.ShiftByRational
