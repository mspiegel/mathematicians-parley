module

public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/abs-limit-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AbsLimitZero.AbsLimitZero

set_option maxHeartbeats 400000 in
theorem abs_limit_zero (a : ℤ → ℝ) (hH2 : Filter.Tendsto (fun n : ℤ => (abs (a n) : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. def:tends-to L := 0, from H2
    have s1_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (abs (a n) - 0) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => abs (a n))) (L := (0 : ℝ)))).mp hH2
    -- 1.2. instantiate ε := ε in line 1.1, from A1
    have s1_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (abs (a n)) < ε) := by simpa only [sub_zero] using (s1_1 ε (by parley_side))
    -- 1.3. obtain N from line 1.2
    obtain ⟨N, s1_3a, s1_3b⟩ := s1_2
    -- 1.4. proof
    have s1_4 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n) < ε := by
      intro n hK2
      intro hA2
      -- 1.4.1. instantiate n := n in line 1.3, from A2
      have s1_4_1 : abs (abs (a n)) < ε := by exact (s1_3b n (by parley_side) (by parley_side))
      -- 1.4.2. membership, from H1
      -- 1.4.3. mun:abs-nonneg x := a(n), from 1.4.2
      have s1_4_3 : abs (a n) ≥ 0 := by exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a n : ℂ)))
      -- 1.4.4. mun:abs-real x := a(n), from 1.4.2
      -- 1.4.5. def:abs x := |a(n)|, from 1.4.3, 1.4.4
      have s1_4_5 : abs (abs (a n)) = abs (a n) := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs (a n))) s1_4_3
      -- 1.4.6. substitute ||a(n)|| = |a(n)| (line 1.4.5) into line 1.4.1
      parley_subst_at s1_4_5 s1_4_1
    -- 1.5. exhibit, from 1.4
    exact ⟨N, s1_3a, s1_4⟩
  -- 2. def:tends-to L := 0, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by simpa only [sub_zero] using s1)

end Parley.Proofs.Hammack.AbsLimitZero.AbsLimitZero
