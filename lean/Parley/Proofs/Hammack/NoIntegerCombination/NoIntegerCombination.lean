module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/no-integer-combination.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NoIntegerCombination.NoIntegerCombination

theorem no_integer_combination :
    ¬ (∃ a : ℤ, ∃ b : ℤ, 21 * a + 30 * b = 1) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain a, b from S
  obtain ⟨a, b, s1⟩ := hS
  -- 2. def:divides d := 3, n := 21
  have r16_1 : (21 : ℤ) = 3 * 7 := by parley_arith
  have s2 : (3 : ℤ) ∣ (21 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (21 : ℤ)))).mpr ⟨(7 : ℤ), by parley_side⟩
  -- 3. def:divides d := 3, n := 30
  have r20_1 : (30 : ℤ) = 3 * 10 := by parley_arith
  have s3 : (3 : ℤ) ∣ (30 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := (30 : ℤ)))).mpr ⟨(10 : ℤ), by parley_side⟩
  -- 4. mun:divides-combination e := 3, a := 21, b := 30, x := a, y := b, from 2, 3
  have s4 : (3 : ℤ) ∣ 21 * a + 30 * b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (3 : ℤ)) (a := (21 : ℤ)) (b := (30 : ℤ)) (x := a) (y := b) s2 s3)
  -- 5. substitute 21a + 30b = 1 (line 1) into line 4
  have s5 : (3 : ℤ) ∣ (1 : ℤ) := by parley_subst_at s1 s4
  -- 6. mun:divides-one d := 3, from 5
  have s6 : (3 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (3 : ℤ)) (by parley_side) s5)
  exact absurd s6 (by norm_num)

end Parley.Proofs.Hammack.NoIntegerCombination.NoIntegerCombination
