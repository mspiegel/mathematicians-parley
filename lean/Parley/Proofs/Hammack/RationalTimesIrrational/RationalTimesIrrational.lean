module

public import AlgebraTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/rational-times-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalTimesIrrational.RationalTimesIrrational

theorem rational_times_irrational (a : ℝ) (b : ℝ) (hH3 : ∃ m : ℚ, (m : ℝ) = a) (hH4 : Irrational (a * b)) :
    Irrational b := by
  -- 1. contradiction
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = b) := by
    intro hS
    -- 1.1. obtain p, q: def:rational x := a, from H3
    obtain ⟨p, q, s1_1a, s1_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := a))).mp hH3
    -- 1.2. obtain r, s: def:rational x := b, from S
    obtain ⟨r, s, s1_2a, s1_2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := b))).mp hS
    -- 1.3. calculation
    have s1_3 : a * b = (p : ℝ) * (r : ℝ) / ((q : ℝ) * (s : ℝ)) := by
      calc a * b = (p : ℝ) / (q : ℝ) * b := by (have h := congrArg (fun t : ℝ => t * b) s1_1b; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (p : ℝ) / (q : ℝ) * ((r : ℝ) / (s : ℝ)) := by (have h := congrArg (fun t : ℝ => (p : ℝ) / (q : ℝ) * t) s1_2b; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (p : ℝ) * (r : ℝ) / ((q : ℝ) * (s : ℝ)) := by parley_ring
    -- 1.4. def:rational x := a·b, from 1.3
    have s1_4 : ∃ m : ℚ, (m : ℝ) = a * b := ((Parley.Items.Stdlib.Numbers.def_rational (x := a * b))).mpr ⟨p * r, q * s, mul_pos (s1_1a) (s1_2a), by (have h := s1_3; push_cast at h ⊢; all_goals exact h)⟩
    -- 1.5. def:irrational x := a·b, from H4
    have s1_5 : ¬ (∃ m : ℚ, (m : ℝ) = a * b) := by exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := a * b))).mp hH4).2
    -- 1.6. restate 1.5
    have s1_6 : ¬ (∃ m : ℚ, (m : ℝ) = a * b) := by exact s1_5
    exact s1_6 s1_4
  -- 2. def:irrational x := b, from 1
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := b))).mpr ⟨by parley_side, s1⟩

end Parley.Proofs.Hammack.RationalTimesIrrational.RationalTimesIrrational
