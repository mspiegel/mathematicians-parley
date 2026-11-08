module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/odd-before-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddBeforeEven.OddBeforeEven

theorem odd_before_even (N : ℤ) :
    (Odd N ↔ (2 : ℤ) ∣ N + 1) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain k: def:odd, from D1
    obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp hD1
    -- 2. algebra, from 1
    have s2 : N + 1 = 2 * (k + 1) := by linear_combination (norm := parley_norm) s1
    -- 3. def:divides d := 2, n := N + 1, from 2
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N + 1))).mpr ⟨k + 1, s2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N + 1))).mpr ⟨k + 1, s2⟩; parley_side)
  · skip
    intro hD2
    -- 4. obtain j: def:divides d := 2, n := N + 1, from D2
    obtain ⟨j, s4⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N + 1))).mp hD2
    -- 5. algebra, from 4
    have s5 : N = 2 * (j - 1) + 1 := by linear_combination (norm := parley_norm) s4
    -- 6. def:odd n := N, from 5
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨j - 1, s5⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨j - 1, s5⟩; parley_side)

end Parley.Proofs.Setmm.OddBeforeEven.OddBeforeEven
