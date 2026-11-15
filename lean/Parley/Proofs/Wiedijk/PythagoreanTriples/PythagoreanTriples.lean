module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Proofs.Wiedijk.PythagoreanTriples
public import Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters
public import Parley.Proofs.Wiedijk.PythagoreanTriples.TripleParameters

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.PythagoreanTriples

theorem pythagorean_triples (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) :
    (a ^ 2 + b ^ 2 = c ^ 2 ↔ (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = k * (m ^ 2 + n ^ 2) ∧ ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ)))))) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:triple-parameters, from D1
    exact (Parley.Proofs.Wiedijk.PythagoreanTriples.TripleParameters.triple_parameters (a := a) hH1 (b := b) hH2 (c := c) hH3 hD1)
  · skip
    intro hD2
    -- 2. D0, from D2
    have s2 : ∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = k * (m ^ 2 + n ^ 2) ∧ ({a, b} : Set ℤ) = ({k * (m ^ 2 - n ^ 2), 2 * k * m * n} : Set ℤ)))) := hD2
    -- 3. obtain k, m, n from line 2
    obtain ⟨k, s3a, m, s3b, n, s3c, ⟨s3d, s3e⟩⟩ := s2
    -- 4. thm:triple-from-parameters, from 3
    exact (Parley.Proofs.Wiedijk.PythagoreanTriples.TripleFromParameters.triple_from_parameters (a := a) hH1 (b := b) hH2 (c := c) hH3 (k := k) s3a (m := m) s3b (n := n) s3c s3d s3e)

end Parley.Proofs.Wiedijk.PythagoreanTriples.PythagoreanTriples
