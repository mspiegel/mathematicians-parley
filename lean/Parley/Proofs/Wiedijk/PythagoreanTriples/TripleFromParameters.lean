module

public import AlgebraTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters

theorem triple_from_parameters (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (k : ℤ) (hH4 : 0 < k) (m : ℤ) (hH5 : 0 < m) (n : ℤ) (hH6 : 0 < n) (hH7 : c = k * (m ^ 2 + n ^ 2)) (hH8 : ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ)) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  -- 1. mun:pair-equal c := k(m² − n²), d := 2kmn, from H8
  have s1 : a = k * (m ^ 2 - n ^ 2) ∧ b = 2 * k * m * n ∨ a = 2 * k * m * n ∧ b = k * (m ^ 2 - n ^ 2) := by exact ((Parley.Items.Stdlib.Sets.mun_pair_equal (a := a) (b := b) (c := k * (m ^ 2 - n ^ 2)) (d := 2 * k * m * n))).mp (by parley_set_side)
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. calculation
    calc a ^ 2 + b ^ 2 = (k * (m ^ 2 - n ^ 2)) ^ 2 + b ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2 + b ^ 2) hC1.1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (k * (m ^ 2 - n ^ 2)) ^ 2 + (2 * k * m * n) ^ 2 := by (have h := congrArg (fun t : ℤ => (k * (m ^ 2 - n ^ 2)) ^ 2 + t ^ 2) hC1.2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (k * (m ^ 2 + n ^ 2)) ^ 2 := by parley_ring
      _ = c ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2) hH7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  · skip
    -- 2.2. calculation
    calc a ^ 2 + b ^ 2 = (2 * k * m * n) ^ 2 + b ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2 + b ^ 2) hC2.1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (2 * k * m * n) ^ 2 + (k * (m ^ 2 - n ^ 2)) ^ 2 := by (have h := congrArg (fun t : ℤ => (2 * k * m * n) ^ 2 + t ^ 2) hC2.2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (k * (m ^ 2 + n ^ 2)) ^ 2 := by parley_ring
      _ = c ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2) hH7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters
