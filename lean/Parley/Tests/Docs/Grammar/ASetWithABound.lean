module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.ASetWithABound

theorem a_set_with_a_bound (S : Set ℝ) (hH1 : S ⊆ (Set.univ : Set ℝ)) (hH2 : (0 : ℝ) ∈ S) (hH3 : ∀ s ∈ S, s ≤ 1) :
    (∃ c : ℝ, (∀ s ∈ S, s ≤ c) ∧ (∀ u : ℝ, (∀ s ∈ S, s ≤ u) → c ≤ u)) := by
  -- 1. exhibit, from H2
  have s1 : ∃ s ∈ S, True := ⟨(0 : ℝ), hH2, trivial⟩
  -- 2. def:upper-bound u := 1, from H3
  have s2 : ∀ s ∈ S, s ≤ 1 := hH3
  -- 3. exhibit, from 2
  have s3 : ∃ u : ℝ, ∀ s ∈ S, s ≤ u := ⟨(1 : ℝ), s2⟩
  -- 4. axi:completeness, from H1, 1, 3
  exact (Parley.Items.Stdlib.Calculus.axi_completeness (S := S) hH1 s1 s3)

end Parley.Tests.Docs.Grammar.ASetWithABound
