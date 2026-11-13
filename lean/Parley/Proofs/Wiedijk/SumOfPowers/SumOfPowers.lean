module

public import AlgebraTactics
public import InstanceTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Polynomials
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/sum-of-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.SumOfPowers.SumOfPowers

theorem sum_of_powers (k : ℤ) (hH1 : 0 ≤ k) (m : ℤ) (hH2 : 0 ≤ m) :
    (∑ n ∈ Finset.Icc (0 : ℤ) m, ((n : ℂ) ^ k.toNat : ℂ)) = (Polynomial.aeval ((m : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (0 : ℂ) (Polynomial.bernoulli (k + 1).toNat)) / ((k : ℂ) + 1) := by
  -- 1. proof
  have s1 : ∀ n : ℤ, n ∈ Finset.Icc 0 m → Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) = ((k : ℂ) + 1) * (n : ℂ) ^ k.toNat := by
    intro n hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 1.1. thm:bernoulli-difference n := k + 1, x := n
    have r20_1 : 0 < k + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := k) hH1)
    have s1_1 : Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) = ((k : ℂ) + 1) * (n : ℂ) ^ (k + 1 - 1) := by
      have hI : Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) = ((k : ℂ) + 1) * (n : ℂ) ^ (k + 1 - 1) := by parley_instance ((Parley.Items.Stdlib.Polynomials.thm_bernoulli_difference (n := k + 1) r20_1 (x := (n : ℂ))))
      exact hI
    -- 1.2. substitute
    have c1 : k + 1 - 1 = k := by parley_ring
    have row1 : Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) = ((k : ℂ) + 1) * (n : ℂ) ^ k.toNat := by (have h := Eq.subst (motive := (fun t : ℤ => Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) = ((k : ℂ) + 1) * (n : ℂ) ^ t)) c1 s1_1; simp only [parley_zpow_toNat (n := k) (h := hH1)] at h ⊢; exact_mod_cast h)
    exact row1
  -- 2. calculation
  have r29_1 : m + 1 ≥ 0 := by linarith only [hH2]
  have s2 : ((k : ℂ) + 1) * (∑ n ∈ Finset.Icc (0 : ℤ) m, ((n : ℂ) ^ k.toNat : ℂ)) = Polynomial.aeval ((m : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (0 : ℂ) (Polynomial.bernoulli (k + 1).toNat) := by
    calc ((k : ℂ) + 1) * (∑ n ∈ Finset.Icc (0 : ℤ) m, ((n : ℂ) ^ k.toNat : ℂ)) = (∑ n ∈ Finset.Icc (0 : ℤ) m, (((k : ℂ) + 1) * (n : ℂ) ^ k.toNat : ℂ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_scaled (t := (fun n : ℤ => (n : ℂ) ^ k.toNat)) (a := (0 : ℤ)) (b := m) (c := (k : ℂ) + 1))
      _ = (∑ n ∈ Finset.Icc (0 : ℤ) m, (Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat) : ℂ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise_complex (t := (fun n : ℤ => ((k : ℂ) + 1) * (n : ℂ) ^ k.toNat)) (u := (fun n : ℤ => Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat))) (a := (0 : ℤ)) (b := m) (fun n h_n => (s1 n h_n).symm))
      _ = Polynomial.aeval ((m : ℂ) + 1) (Polynomial.bernoulli (k + 1).toNat) - Polynomial.aeval (0 : ℂ) (Polynomial.bernoulli (k + 1).toNat) := by exact_mod_cast (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli (k + 1).toNat))) (a := (0 : ℤ)) (b := m) r29_1)
  -- 3. algebra, from 2
  have r36_1 : 0 < k + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := k) hH1)
  linear_combination (norm := parley_field) ((1) / (((k : ℂ) + 1))) * s2

end Parley.Proofs.Wiedijk.SumOfPowers.SumOfPowers
