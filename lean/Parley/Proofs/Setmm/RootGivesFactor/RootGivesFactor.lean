module

public import Polynomials
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Polynomials

/-! Written from proofs/setmm/root-gives-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RootGivesFactor.RootGivesFactor

theorem root_gives_factor (p : ℂ → ℂ) (hH1 : p ∈ LeanBridges.Polynomials.polynomials) (a : ℂ) (hH3 : p a = 0) :
    (∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x)) := by
  -- 1. obtain q: thm:remainder, from H1
  obtain ⟨q, s1a, s1b⟩ := (Parley.Items.Stdlib.Polynomials.thm_remainder (p := p) hH1 (a := a))
  -- 2. proof
  have s2 : ∀ x : ℂ, p x = (x - a) * q x := by
    intro x
    -- 2.1. substitute p(a) = 0 (H3) into line 1
    have at0 := (s1b x)
    parley_subst_at hH3 at0
  -- 3. exhibit, from 1, 2
  exact ⟨q, by parley_side, by parley_side⟩

end Parley.Proofs.Setmm.RootGivesFactor.RootGivesFactor
