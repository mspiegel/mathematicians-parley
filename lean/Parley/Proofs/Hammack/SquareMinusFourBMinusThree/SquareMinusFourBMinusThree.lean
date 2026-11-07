module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/square-minus-four-b-minus-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareMinusFourBMinusThree.SquareMinusFourBMinusThree

set_option maxHeartbeats 400000 in
theorem square_minus_four_b_minus_three (a : ℤ) (b : ℤ) :
    a ^ 2 - 4 * b - 3 ≠ 0 := by
  -- the theorem. contradiction
  have sThm : a ^ 2 - 4 * b - 3 ≠ 0 := by
    by_contra hc_hS
    have hS : a ^ 2 - 4 * b - 3 = 0 := by parley_suppose hc_hS
    -- 1. algebra, from S
    have s1 : a ^ 2 = 4 * b + 3 := by linear_combination (norm := parley_norm) hS
    -- 2. mun:even-or-odd n := a
    have s2 : Even a ∨ Odd a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := a)); parley_side)
    -- 3. cases, from 2
    have s3 : Even (1 : ℤ) := by
      rcases s2 with hC1 | hC2
      · skip
        -- 3.1. obtain k: def:even n := a, from C1
        obtain ⟨k, s3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
        -- 3.2. calculation
        have s3_2 : 4 * k ^ 2 = 4 * b + 3 := by
          calc 4 * k ^ 2 = (2 * k) ^ 2 := by parley_ring
            _ = a ^ 2 := by parley_subst s3_1
            _ = 4 * b + 3 := by parley_side
        -- 3.3. algebra, from 3.2
        have s3_3 : 1 = 2 * (2 * k ^ 2 - 2 * b - 1) := by linear_combination (norm := parley_norm) (-1) * s3_2
        -- 3.4. def:even n := 1, from 3.3
        have s3_4 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨2 * k ^ 2 - 2 * b - 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨2 * k ^ 2 - 2 * b - 1, by parley_side⟩; parley_side)
        all_goals parley_side
      · skip
        -- 3.5. obtain k: def:odd n := a, from C2
        obtain ⟨k, s3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
        -- 3.6. calculation
        have s3_6 : 4 * k ^ 2 + 4 * k + 1 = 4 * b + 3 := by
          calc 4 * k ^ 2 + 4 * k + 1 = (2 * k + 1) ^ 2 := by parley_ring
            _ = a ^ 2 := by parley_subst s3_5
            _ = 4 * b + 3 := by parley_side
        -- 3.7. algebra, from 3.6
        have s3_7 : 1 = 2 * (k ^ 2 + k - b) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 2 : ℚ)) * s3_6
        -- 3.8. def:even n := 1, from 3.7
        have s3_8 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k ^ 2 + k - b, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k ^ 2 + k - b, by parley_side⟩; parley_side)
        all_goals parley_side
    -- 4. mun:not-both n := 1, from 3
    have s4 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s3); parley_side)
    -- 5. arithmetic
    have s5 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquareMinusFourBMinusThree.SquareMinusFourBMinusThree
