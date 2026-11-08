module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/two-does-not-divide-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoDoesNotDivideOdd.TwoDoesNotDivideOdd

theorem two_does_not_divide_odd (A : ℤ) :
    ¬ (2 : ℤ) ∣ 2 * A + 1 := by
  set B : ℤ := 2 * A + 1 with hD1
  -- the theorem. contradiction
  intro hS
  -- 1. obtain k: def:divides d := 2, n := B, from S
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := B))).mp hS
  -- 2. algebra, from D1, 1
  have s2 : 2 * (k - A) = 1 := by
    try simp only [hD1] at *
    try push_cast at *
    linear_combination (norm := parley_norm) (-1) * s1
  -- 3. def:divides d := 2, n := 1, from 2
  have s3 : (2 : ℤ) ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨k - A, s2.symm⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨k - A, s2.symm⟩; parley_side)
  -- 4. mun:divides-one d := 2, from 3
  have s4 : (2 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (2 : ℤ)) (by parley_side) s3)
  exact absurd s4 (by norm_num)

end Parley.Proofs.Setmm.TwoDoesNotDivideOdd.TwoDoesNotDivideOdd
