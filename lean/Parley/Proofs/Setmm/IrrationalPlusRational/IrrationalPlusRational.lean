module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/irrational-plus-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IrrationalPlusRational.IrrationalPlusRational

set_option maxHeartbeats 400000 in
theorem irrational_plus_rational (A : ℝ) (B : ℝ) (hH3 : A ∈ (Set.univ : Set ℝ) \ {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (hH4 : ∃ m : ℚ, (m : ℝ) = B) :
    A + B ∈ (Set.univ : Set ℝ) \ {x : ℝ | ∃ m : ℚ, (m : ℝ) = x} := by
  -- 1. def:difference Y := ℝ, Z := ℚ, from H3
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by simpa only [Int.cast_id, Set.mem_setOf_eq] using (((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A))).mp hH3).2
  -- 2. obtain p, q: def:rational x := B, from H4
  obtain ⟨p, q, s2a, s2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp hH4
  -- 3. contradiction
  have s3 : ¬ (∃ m : ℚ, (m : ℝ) = A + B) := by
    intro hS
    -- 3.1. obtain r, s: def:rational x := A + B, from S
    obtain ⟨r, s, s3_1a, s3_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A + B))).mp hS
    -- 3.2. algebra, from 1, 3.1
    have s3_2 : A = (r : ℝ) / (s : ℝ) - B := by linear_combination (norm := parley_field) s3_1b
    -- 3.3. substitute B = p/q (line 2) into line 3.2
    have s3_3 : A = (r : ℝ) / (s : ℝ) - (p : ℝ) / (q : ℝ) := by parley_subst_at s2b s3_2
    -- 3.4. calculation
    have s3_4 : A = ((r : ℝ) * (q : ℝ) - (p : ℝ) * (s : ℝ)) / ((s : ℝ) * (q : ℝ)) := by
      calc A = (r : ℝ) / (s : ℝ) - (p : ℝ) / (q : ℝ) := by parley_set_side
        _ = ((r : ℝ) * (q : ℝ) - (p : ℝ) * (s : ℝ)) / ((s : ℝ) * (q : ℝ)) := by parley_ring
    -- 3.5. exhibit, from 3.4
    have s3_5 : ∃ a : ℤ, ∃ b : ℤ, 0 < b ∧ A = (a : ℝ) / (b : ℝ) := ⟨r * q - p * s, s * q, by parley_set_side, by first | exact_mod_cast s3_4 | (have h := s3_4; push_cast at h ⊢; exact h) | simpa using s3_4⟩
    -- 3.6. def:rational x := A, from 3.5
    have s3_6 : ∃ m : ℚ, (m : ℝ) = A := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mpr s3_5
    exact s1 s3_6
  -- 4. mun:real-closure x := A, y := B, from 1
  -- 5. def:difference Y := ℝ, Z := ℚ, from 3, 4
  exact ((Parley.Items.Stdlib.Sets.def_difference (Y := (Set.univ : Set ℝ)) (Z := {x : ℝ | ∃ m : ℚ, (m : ℝ) = x}) (u := A + B))).mpr (by parley_set_side)

end Parley.Proofs.Setmm.IrrationalPlusRational.IrrationalPlusRational
