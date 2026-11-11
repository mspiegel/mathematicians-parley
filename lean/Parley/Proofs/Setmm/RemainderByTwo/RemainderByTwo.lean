module

public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/remainder-by-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderByTwo.RemainderByTwo

theorem remainder_by_two (N : ℤ) :
    (N % (2 : ℤ) = 1 ↔ ¬ (2 : ℤ) ∣ N) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain q: mun:mod-remainder a := N, m := 2, r := 1, from D1
    have r18_1 : (1 : ℤ) < 2 := by parley_arith
    obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := N) (m := (2 : ℤ)) (by parley_side) (r := (1 : ℤ)) (by parley_side) r18_1)).mp hD1
    -- 2. algebra, from 1
    have s2 : N = 2 * q + 1 := by linear_combination (norm := parley_norm) (-1) * s1
    -- 3. def:odd n := N, from 2
    have s3 : Odd N := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨q, s2⟩
    -- 4. contradiction
    intro hS1
    -- 4.1. obtain k: def:divides d := 2, n := N, from S1
    obtain ⟨k, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N))).mp hS1
    -- 4.2. def:even n := N, from 4.1
    have s4_2 : Even N := ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mpr ⟨k, s4_1⟩
    -- 4.3. mun:not-both n := N, from 4.2
    have s4_3 : ¬ Odd N := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := N) s4_2)
    exact s4_3 s3
  · skip
    intro hD2
    -- 5. contradiction
    have s5 : ¬ Even N := by
      intro hS2
      -- 5.1. obtain k: def:even n := N, from S2
      obtain ⟨k, s5_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := N))).mp hS2
      -- 5.2. def:divides d := 2, n := N, from 5.1
      have s5_2 : (2 : ℤ) ∣ N := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N))).mpr ⟨k, s5_1⟩
      exact hD2 s5_2
    -- 6. mun:even-or-odd
    have s6 : Even N ∨ Odd N := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := N))
    -- 7. mun:disjunctive-syllogism-left P := N is even, Q := N is odd, from 5, 6
    have s7 : Odd N := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even N) (Q := Odd N) s6 s5)
    -- 8. obtain k: def:odd, from 7
    obtain ⟨k, s8⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp s7
    -- 9. algebra, from 8
    have s9 : k * 2 + 1 = N := by linear_combination (norm := parley_norm) (-1) * s8
    -- 10. exhibit, from 9
    have s10 : ∃ q : ℤ, q * 2 + 1 = N := ⟨k, s9⟩
    -- 11. mun:mod-remainder a := N, m := 2, r := 1, from 10
    have r69_1 : (1 : ℤ) < 2 := by parley_arith
    exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := N) (m := (2 : ℤ)) (by parley_side) (r := (1 : ℤ)) (by parley_side) r69_1)).mpr s10

end Parley.Proofs.Setmm.RemainderByTwo.RemainderByTwo
