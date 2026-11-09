module

public import AlgebraTactics
public import SubstTactics
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
    have s2_1 : ∃ m : ℚ, (m : ℝ) = A * (B : ℝ) / (B : ℝ) := by rw [← Classical.choose_spec hS]; (try rw [← Classical.choose_spec hS] at hH3; norm_cast at hH3); (first | exact (Parley.Proofs.Setmm.RationalClosure.RationalQuotient.rational_quotient (A := (Classical.choose hS)) (B := B) hH3) | exact ((Parley.Proofs.Setmm.RationalClosure.RationalQuotient.rational_quotient (A := (Classical.choose hS)) (B := B) hH3)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.RationalQuotient.rational_quotient (A := (Classical.choose hS)) (B := B) hH3) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.RationalQuotient.rational_quotient (A := (Classical.choose hS)) (B := B) hH3) | (have h := (Parley.Proofs.Setmm.RationalClosure.RationalQuotient.rational_quotient (A := (Classical.choose hS)) (B := B) hH3); parley_side))
    -- 2.2. substitute
    have s2_2 : ∃ m : ℚ, (m : ℝ) = A := by
      have c1 : A * (B : ℝ) / (B : ℝ) = A := by parley_ring
      have row1 : ∃ m : ℚ, (m : ℝ) = A := by parley_subst_at c1 s2_1
      exact row1
    -- 2.3. restate 1
    have s2_3 : ¬ (∃ m : ℚ, (m : ℝ) = A) := by parley_side
    exact s2_3 s2_2
  -- 3. def:irrational x := A·B, from 2
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := A * (B : ℝ)))).mpr (by parley_side)

end Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
