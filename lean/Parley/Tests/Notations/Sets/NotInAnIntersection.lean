module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.NotInAnIntersection

theorem not_in_an_intersection :
    ¬ (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∩ ({(3 : ℤ)} : Set ℤ) := by
  -- 1. arithmetic
  have s1 : (3 : ℤ) ≠ 1 := by norm_num
  -- 2. arithmetic
  have s2 : (3 : ℤ) ≠ 2 := by norm_num
  -- 3. contradiction
  have s3 : ¬ (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by
    intro hS
    -- 3.1. def:pair x := 3, u := 1, w := 2, from S
    have s3_1 : (3 : ℤ) = 1 ∨ (3 : ℤ) = 2 := by exact ((Parley.Items.Stdlib.Sets.def_pair (u := (1 : ℤ)) (w := (2 : ℤ)) (x := (3 : ℤ)))).mp hS
    -- 3.2. mun:disjunctive-syllogism, from 2, 3.1
    have s3_2 : (3 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (3 : ℤ) = 1) (Q := (3 : ℤ) = 2) s3_1 s2)
    exact s1 s3_2
  -- 4. contradiction
  intro hS
  -- 4.1. def:intersection, from S
  have s4_1 : (3 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := ({(1 : ℤ), (2 : ℤ)} : Set ℤ)) (Z := ({(3 : ℤ)} : Set ℤ)) (u := (3 : ℤ)))).mp hS).1
  exact s3 s4_1

end Parley.Tests.Notations.Sets.NotInAnIntersection
