module

public import AlgebraTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.RationalClosure.RationalQuotient

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.IrrationalProduct

theorem irrational_product (A : ℝ) (B : ℚ) (hH3 : B ≠ 0) (hH4 : Irrational A) :
    Irrational (A * (B : ℝ)) := by
  -- 1. def:irrational x := A, from H4
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := A))).mp hH4).2
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = A * (B : ℝ)) := by
    intro hS
    -- 2.1. thm:rational-quotient A := A·B, from H3, S
    have s2_1 : ∃ m : ℚ, (m : ℝ) = A * (B : ℝ) / (B : ℝ) := by (exact ⟨(Classical.choose hS : ℚ) / B, by push_cast; (try simp only [Classical.choose_spec hS]); all_goals parley_ring⟩)
    -- 2.2. substitute
    have s2_2 : ∃ m : ℚ, (m : ℝ) = A := by
      have c1 : A * (B : ℝ) / (B : ℝ) = A := by parley_ring
      have row1 : ∃ m : ℚ, (m : ℝ) = A := by (have h := Eq.subst (motive := (fun t : ℝ => ∃ m : ℚ, (m : ℝ) = t)) c1 s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 2.3. restate 1
    have s2_3 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by exact s1
    exact s2_3 s2_2
  -- 3. def:irrational x := A·B, from 2
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := A * (B : ℝ)))).mpr ⟨by trivial, s2⟩

end Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
