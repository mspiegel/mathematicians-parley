module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/power-nonnegative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerNonnegative.PowerNonnegative

theorem power_nonnegative (a : ℝ) (n : ℕ) (hH3 : 0 ≤ a) :
    0 ≤ a ^ n := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, 0 ≤ a ^ m := by
    intro m
    induction m with
    | zero =>
      -- 1.1. algebra
      have s1_1 : a ^ 0 = 1 := by ring
      -- 1.2. arithmetic
      have s1_2 : (0 : ℤ) ≤ 1 := by parley_arith
      -- 1.3. transitivity, from 1.2, 1.1
      have s1_3 : 0 ≤ a ^ 0 := by parley_side
      all_goals parley_side
    | succ m hIH =>
      -- 1.4. mun:exponent-step
      have s1_4 : a ^ (m + 1) = a ^ m * a := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m))
      -- 1.5. axi:trichotomy x := a
      have s1_5 : (a < 0 ∨ a = 0) ∨ 0 < a := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a))
      -- 1.6. cases, from 1.5
      have s1_6 : 0 ≤ a ^ (m + 1) := by
        rcases s1_5 with (hC1 | hC2) | hC3
        · skip
          -- 1.6.1. inequalities, from C1
          have s1_6_1 : ¬ 0 ≤ a := by parley_side
          all_goals parley_side
        · skip
          -- 1.6.2. algebra, from C2
          have s1_6_2 : a ^ m * a = 0 := by linear_combination (a ^ m) * hC2
          -- 1.6.3. transitivity, from 1.6.2, 1.4
          have s1_6_3 : 0 = a ^ (m + 1) := by parley_side
          -- 1.6.4. inequalities
          have s1_6_4 : 0 ≤ a ^ (m + 1) := by parley_side
          all_goals parley_side
        · skip
          -- 1.6.5. mun:multiply-le x := 0, y := a^m, c := a, from C3, IH
          have s1_6_5 : a * 0 ≤ a * a ^ m := by linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (0 : ℝ)) (y := a ^ m) (c := a) (by parley_side) (by parley_side))]
          -- 1.6.6. inequalities
          have s1_6_6 : 0 ≤ a ^ m * a := by parley_side
          -- 1.6.7. transitivity, from 1.6.6, 1.4
          have s1_6_7 : 0 ≤ a ^ (m + 1) := by parley_side
          all_goals parley_side
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : 0 ≤ a ^ n := by linarith [(s1 n)]
  all_goals parley_side

end Parley.Proofs.Setmm.PowerNonnegative.PowerNonnegative
