module

public import Polynomials
public import Tactics
public import Parley.Items.Stdlib.Polynomials

/-! Written from proofs/setmm/factor-by-root.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorByRoot.FactorByRoot

theorem factor_by_root (p : ℂ → ℂ) (hH1 : p ∈ LeanBridges.Polynomials.polynomials) (a : ℂ) (hH3 : p a = 0) :
    (∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x)) := by
  -- 1. obtain q: thm:remainder, from H1
  obtain ⟨q, s1a, s1b⟩ := (Parley.Items.Stdlib.Polynomials.thm_remainder (p := p) hH1 (a := a))
  -- 2. proof
  have s2 : ∀ x : ℂ, p x = (x - a) * q x := by
    intro x
    -- 2.1. substitute p(a) = 0 (H3) into line 1
    have s2_1 : p x = (x - a) * q x := by parley_subst_at hH3 s1b
    all_goals exact s2_1
  -- 3. exhibit, from 1, 2
  have s3 : ∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x) := ⟨q, by parley_side, by parley_side⟩
  all_goals exact s3

end Parley.Proofs.Setmm.FactorByRoot.FactorByRoot
