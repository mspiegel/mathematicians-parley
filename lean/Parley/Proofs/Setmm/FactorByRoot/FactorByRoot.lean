module

public import Polynomials
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
    (have h := Eq.subst (motive := (fun t : ℂ => p x = (x - a) * q x + t)) hH3 (s1b x); push_cast [add_zero] at h ⊢; exact_mod_cast h)
  -- 3. exhibit, from 1, 2
  exact ⟨q, s1a, s2⟩

end Parley.Proofs.Setmm.FactorByRoot.FactorByRoot
