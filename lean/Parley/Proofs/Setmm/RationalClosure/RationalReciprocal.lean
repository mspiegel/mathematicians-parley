module

public import AlgebraTactics
public import ArithTactics
public import SubstTactics
public import Tactics
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
    by_contra hc_hS
    have hS : p = 0 := by parley_suppose hc_hS
    -- 2.1. substitute p = 0 (S) into line 1
    have s2_1 : A = 0 / (q : ℚ) := by
      have hS_w : (p : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hS; push_cast at h; linear_combination (norm := parley_norm) h
      first | parley_subst_at hS_w s1b | parley_subst_at hS s1b
    -- 2.2. calculation
    have s2_2 : A = 0 := by
      calc A = 0 / (q : ℚ) := by parley_side
        _ = 0 := by parley_ring
    -- 2.3. restate H2
    have s2_3 : A ≠ 0 := by parley_side
    all_goals parley_side
  -- 3. axi:trichotomy x := p
  have s3 : (p < 0 ∨ p = 0) ∨ 0 < p := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p)) | (have h := (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := p)); parley_side)
  -- 4. cases, from 3
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalReciprocal
