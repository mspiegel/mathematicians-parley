module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-times-denominator.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalTimesDenominator.RationalTimesDenominator

theorem rational_times_denominator (A : ℚ) :
    (∃ x : ℤ, 0 < x ∧ (∃ m : ℤ, (m : ℚ) = A * (x : ℚ))) := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp ⟨_, rfl⟩
  -- 2. algebra, from 1
  have s2 : A * (q : ℚ) = (p : ℚ) := by have hz1 : (q : ℚ) ≠ 0 := (by positivity); linear_combination (norm := (field)) ((q : ℚ)) * s1b
  -- 3. membership, from 2
  have s3 : ∃ m : ℤ, (m : ℚ) = A * (q : ℚ) := ⟨p, by exact_mod_cast (s2).symm⟩
  -- 4. exhibit, from 3
  exact ⟨q, s1a, s3⟩

end Parley.Proofs.Setmm.RationalTimesDenominator.RationalTimesDenominator
