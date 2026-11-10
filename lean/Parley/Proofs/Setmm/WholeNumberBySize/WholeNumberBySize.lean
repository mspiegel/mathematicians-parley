module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/whole-number-by-size.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.WholeNumberBySize.WholeNumberBySize

set_option maxHeartbeats 400000 in
theorem whole_number_by_size (A : ℝ) :
    ((∃ m : ℤ, (m : ℝ) = A) ↔ (∃ m : ℤ, (m : ℝ) = abs A)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. mun:abs-integer z := A, from D1
    have s1 : ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = abs A := by (exact ⟨abs (Classical.choose hD1 : ℤ), by parley_side, by push_cast; (try simp only [Classical.choose_spec hD1]); all_goals parley_ring⟩)
    -- 2. mun:nat0-int m := |A|, from 1
    have whole1 : ∃ m : ℤ, (m : ℝ) = abs A := by obtain ⟨m, _, hm⟩ := s1; exact ⟨m, by exact_mod_cast hm⟩
    exact ⟨(Classical.choose whole1 : ℤ), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring)⟩
  · skip
    intro hD2
    -- 3. mun:nonneg-or-neg x := A
    have s3 : A ≥ 0 ∨ A < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A))
    -- 4. cases, from 3
    rcases s3 with hC1 | hC2
    · skip
      -- 4.1. def:abs x := A, from C1
      have s4_1 : abs A = A := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) hC1
      -- 4.2. substitute |A| = A (line 4.1) into D2
      (have h := Eq.subst (motive := (fun t : ℝ => ∃ m : ℤ, (m : ℝ) = t)) s4_1 hD2; push_cast at h ⊢; all_goals exact_mod_cast h)
    · skip
      -- 4.3. def:abs x := A, from C2
      have s4_3 : abs A = -A := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) hC2
      -- 4.4. substitute |A| = −A (line 4.3) into D2
      have s4_4 : ∃ m : ℤ, (m : ℝ) = -A := by (have h := Eq.subst (motive := (fun t : ℝ => ∃ m : ℤ, (m : ℝ) = t)) s4_3 hD2; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 4.5. membership, from 4.4
      have s4_5 : ∃ m : ℤ, (m : ℝ) = 0 - -A := by
        have whole1 : ∃ m : ℤ, (m : ℝ) = -A := by obtain ⟨m, hm⟩ := s4_4; exact ⟨m, by exact_mod_cast hm⟩
        exact ⟨(0 - (Classical.choose whole1 : ℤ)), by (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring)⟩
      -- 4.6. substitute
      have c1 : 0 - -A = A := by parley_ring
      have row1 : ∃ m : ℤ, (m : ℝ) = A := by parley_subst_at c1 s4_5
      exact row1

end Parley.Proofs.Setmm.WholeNumberBySize.WholeNumberBySize
