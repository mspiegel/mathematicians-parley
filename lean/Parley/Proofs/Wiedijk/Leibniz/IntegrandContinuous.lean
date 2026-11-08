module

public import AlgebraTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous

set_option maxHeartbeats 600000 in
theorem integrand_continuous (n : ℤ) (hH1 : 0 ≤ n) (g : ℝ → ℝ) (hH2 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * n).toNat / (1 + x ^ 2)) :
    ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by
  set u : ℝ → ℝ := fun x => x ^ (2 * n).toNat with hD1
  set o : ℝ → ℝ := fun x => (1 : ℝ) with hD2
  set s : ℝ → ℝ := fun x => x ^ 2 with hD3
  set v : ℝ → ℝ := fun x => 1 + x ^ 2 with hD4
  -- 1. mun:interval-real
  have s1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), u x = x ^ (2 * n).toNat := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), o x = 1 := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 4. D3
  have s4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s x = x ^ 2 := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_set_side
  -- 5. algebra, from D2, D3, D4
  have s5 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), v x = o x + s x := by intro x h_x; parley_ring
  -- 6. membership, from D1
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 7. mun:function-into, from 6
  have s7 : Set.MapsTo u (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := u) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 8. membership, from D2
  have s8 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 9. membership, from D3
  have s9 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 10. membership, from D4
  have s10 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 11. mun:function-into, from 8
  have s11 : Set.MapsTo o (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := o) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 12. mun:function-into, from 9
  have s12 : Set.MapsTo s (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := s) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 13. mun:function-into, from 10
  have s13 : Set.MapsTo v (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := v) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 14. thm:continuous-power D := [0, 1], n := 2n, from 1, 2, 7
  have s14 : ContinuousOn u (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := u) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2)
  -- 15. thm:continuous-constant D := [0, 1], c := 1, from 1, 3, 11
  have s15 : ContinuousOn o (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_constant (g := o) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (c := (1 : ℝ)) (by parley_set_side))
  -- 16. thm:continuous-square D := [0, 1], from 1, 4, 12
  have s16 : ContinuousOn s (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_square (g := s) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s4)
  -- 17. thm:continuous-sum D := [0, 1], f := o, g := s, from 1, 5, 11, 12, 13, 15, 16
  have s17 : ContinuousOn v (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := v) (f := o) (g := s) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s5 s15 s16)
  -- 18. proof
  have s18 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), v x ≠ 0 := by
    intro x hK1
    -- 18.1. mun:square-nonneg
    have s18_1 : x ^ 2 ≥ 0 := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
    -- 18.2. inequalities, from 18.1
    have s18_2 : 1 + x ^ 2 > 0 := by parley_order
    -- 18.3. inequalities
    have s18_3 : 1 + x ^ 2 ≠ 0 := by parley_set_side
    -- 18.4. D4, from K1
    have s18_4 : v x = 1 + x ^ 2 := by first | (simp (disch := omega) only [hD4]; done) | (simp (disch := omega) only [hD4]; push_cast; norm_num; done) | parley_set_side
    -- 18.5. substitute v(x) = 1 + x² (line 18.4) into line 18.3
    parley_subst_at s18_4 s18_3
  -- 19. proof
  have s19 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = u x / v x := by
    intro x hK2
    -- 19.1. instantiate x := x in H3, from D1, D4, K2
    first | linear_combination (norm := parley_norm) (hH3 x (by parley_set_side)) | (have h := (hH3 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3 x (by parley_set_side)) | exact_mod_cast ((hH3 x (by parley_set_side))).symm | (have h := (hH3 x (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3 x (by parley_set_side)); parley_int_power h) | (have h := (hH3 x (by parley_set_side)); parley_set_side)
  -- 20. thm:continuous-quotient D := [0, 1], F := g, f := u, g := v, from 1, 7, 13, 14, 17, 18, 19
  exact (Parley.Items.Stdlib.Calculus.thm_continuous_quotient (F := g) (f := u) (g := v) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s18 s19 s14 s17)

end Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous
