module

public import AlgebraTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.OddHalf

theorem odd_half (N : ℤ) :
    (Odd N ↔ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) - 1) / 2)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain k: def:odd n := N, from D1
    obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp hD1
    -- 2. algebra, from 1
    have s2 : ((N : ℚ) - 1) / 2 = (k : ℚ) := by
      have s1_w : (N : ℚ) = 2 * (k : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
      linear_combination (norm := parley_norm) ((1) / ((2))) * s1_w
    -- 3. membership, from 2
    exact ⟨k, by exact_mod_cast (s2).symm⟩
  · skip
    intro hD2
    -- 4. algebra
    have s4 : (N : ℚ) = 2 * (((N : ℚ) - 1) / 2) + 1 := by parley_ring
    -- 5. def:odd n := N, from D2, 4
    exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨Classical.choose hD2, by have := Classical.choose_spec hD2; qify; rw [this]; linarith only [s4]⟩

end Parley.Proofs.Setmm.Parity.OddHalf
