module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cube-of-sum-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeOfSumModThree.CubeOfSumModThree

theorem cube_of_sum_mod_three (a : ℤ) (b : ℤ) :
    (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD (3 : ℤ)] := by
  -- 1. algebra
  have s1 : (a + b) ^ 3 - (a ^ 3 + b ^ 3) = 3 * (a ^ 2 * b + a * b ^ 2) := by parley_ring
  -- 2. def:divides d := 3, n := (a + b)³ − (a³ + b³), from 1
  have s2 : (3 : ℤ) ∣ (a + b) ^ 3 - (a ^ 3 + b ^ 3) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (a + b) ^ 3 - (a ^ 3 + b ^ 3)))).mpr ⟨a ^ 2 * b + a * b ^ 2, s1⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (a + b) ^ 3 - (a ^ 3 + b ^ 3)))).mpr ⟨a ^ 2 * b + a * b ^ 2, s1⟩; parley_side)
  -- 3. def:congruent-mod n := 3, from 2
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (a + b) ^ 3) (b := a ^ 3 + b ^ 3))).mpr s2 | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := (a + b) ^ 3) (b := a ^ 3 + b ^ 3))).mpr s2; parley_side)

end Parley.Proofs.Hammack.CubeOfSumModThree.CubeOfSumModThree
