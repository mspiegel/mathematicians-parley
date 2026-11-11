module

public import ArithTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus

/-! Written from tests/notations/integrals.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Integrals.AnIntegralOfALine

theorem an_integral_of_a_line (f : ℝ → ℝ) (hH1 : Set.MapsTo f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), f x = 2 * x) (F : ℝ → ℝ) (hH3 : Set.MapsTo F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), F x = x ^ 2) :
    (∫ t in 0..1, (f t : ℝ)) = 1 := by
  -- 1. thm:continuous-linear D := [0, 1], m := 2, from H2
  have r20_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s1 : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) r20_1 (m := (2 : ℝ)) hH2)
  -- 2. thm:continuous-square D := [0, 1], from H4
  have r24_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s2 : ContinuousOn F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_square (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) r24_1 hH4)
  -- 3. mun:open-within-closed a := 0, b := 1
  have s3 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  -- 4. thm:derivative-square D := [0, 1], U := (0, 1), from H4, 3
  have r31_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r31_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s4a : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_square_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) r31_1 s3 r31_2 hH4)
  have s4b : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = 2 * x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_square_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) r31_1 s3 r31_2 hH4)
  -- 5. proof
  have s5 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = f x := by
    intro x hK1
    -- 5.1. mun:in-subset, from K1, 3
    have s5_1 : x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) s3 hK1)
    -- 5.2. instantiate x := x in H2, from 5.1
    have s5_2 : f x = 2 * x := by exact (hH2 x s5_1)
    -- 5.3. instantiate x := x in line 4, from K1
    have s5_3 : (deriv F) x = 2 * x := by exact (s4b x hK1)
    -- 5.4. calculation
    calc (deriv F) x = 2 * x := by exact s5_3
      _ = f x := by exact s5_2.symm
  -- 6. thm:fundamental-calculus a := 0, b := 1, from 1, 2, 4, 5
  have r54_1 : (0 : ℤ) < 1 := by parley_arith
  have s6 : (∫ t in 0..1, (f t : ℝ)) = F 1 - F 0 := by exact (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := f) (by parley_set_side) s1 (F := F) (by parley_set_side) s2 s4a s5)
  -- 7. def:interval a := 0, b := 1, x := 1
  have r58_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r58_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s7 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by parley_set_side, by parley_set_side⟩, by parley_set_side⟩
  -- 8. def:interval a := 0, b := 1, x := 0
  have r63_1 : (0 : ℤ) ≤ 0 := by parley_arith
  have r63_2 : (0 : ℤ) ≤ 1 := by parley_arith
  have s8 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (0 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by parley_set_side, by parley_set_side⟩, by parley_set_side⟩
  -- 9. instantiate x := 1 in H4, from 7
  have s9 : F 1 = 1 ^ 2 := by exact (hH4 (1 : ℝ) s7)
  -- 10. instantiate x := 0 in H4, from 8
  have s10 : F 0 = 0 ^ 2 := by exact (hH4 (0 : ℝ) s8)
  -- 11. substitute F(1) = 1² (line 9) into line 6
  have s11 : (∫ t in 0..1, (f t : ℝ)) = 1 ^ 2 - F 0 := by (have h := Eq.subst (motive := (fun u : ℝ => (∫ t in 0..1, (f t : ℝ)) = u - F 0)) s9 s6; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 12. substitute F(0) = 0² (line 10) into line 11
  have s12 : (∫ t in 0..1, (f t : ℝ)) = 1 ^ 2 - 0 ^ 2 := by (have h := Eq.subst (motive := (fun u : ℝ => (∫ t in 0..1, (f t : ℝ)) = 1 ^ 2 - u)) s10 s11; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 13. calculation
  calc (∫ t in 0..1, (f t : ℝ)) = 1 ^ 2 - 0 ^ 2 := by exact s12
    _ = 1 := by norm_num

end Parley.Tests.Notations.Integrals.AnIntegralOfALine
