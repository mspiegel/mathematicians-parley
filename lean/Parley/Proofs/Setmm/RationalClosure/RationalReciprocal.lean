module

public import AlgebraTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalReciprocal

set_option maxHeartbeats 400000 in
theorem rational_reciprocal (A : ℚ) (hH2 : A ≠ 0) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. contradiction
  have s2 : p ≠ 0 := by
    intro hS
    -- 2.1. substitute p = 0 (S) into line 1
    have s2_1 : A = 0 / (q : ℚ) := by
      have e_w : (p : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hS; push_cast at h; linear_combination (norm := parley_norm) h
      (have h := Eq.subst (motive := (fun t : ℚ => A = t / (q : ℚ))) e_w s1b; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.2. calculation
    have s2_2 : A = 0 := by
      calc A = 0 / (q : ℚ) := by exact s2_1
        _ = 0 := by parley_ring
    -- 2.3. restate H2
    have s2_3 : A ≠ 0 := by parley_side
    exact s2_3 s2_2
  -- 3. axi:trichotomy x := p
  have s3 : (p < 0 ∨ p = 0) ∨ 0 < p := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p))
  -- 4. cases, from 3
  -- what this block shows, Lean's types give
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalReciprocal
