module

public import NormTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/square-divides-itself.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareDividesItself.SquareDividesItself

theorem square_divides_itself (a : ℤ) (hH2 : a ^ 2 ∣ a) :
    a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
  -- 1. obtain k: def:divides d := a², n := a, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 2) (n := a))).mp hH2
  -- 2. axi:excluded-middle P := a = 0
  have s2 : a = 0 ∨ a ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0))
  -- 3. cases, from 2
  rcases s2 with hC1 | hC2
  · skip
    -- 3.1. inspection
    have s3_1 : (0 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
    -- 3.2. substitute a = 0 (C1) into line 3.1
    (have h := Eq.subst (motive := (fun t : ℤ => t ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ))) hC1.symm s3_1; push_cast at h ⊢; all_goals exact_mod_cast h)
  · skip
    -- 3.3. algebra, from 1
    have s3_3 : a * k * a = 1 * a := by linear_combination (norm := parley_norm) (-1) * s1
    -- 3.4. mun:multiply-cancel a := a·k, b := 1, c := a, from C2, 3.3
    have s3_4 : a * k = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) hC2)
    -- 3.5. mun:nonneg-or-neg x := a
    have s3_5 : a ≥ 0 ∨ a < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a))
    -- 3.6. cases, from 3.5
    rcases s3_5 with hC3 | hC4
    · skip
      -- 3.6.1. inequalities, from C2, C3
      have s3_6_1 : a > 0 := by parley_order
      -- 3.6.2. mun:pos-int-nat m := a, from 3.6.1
      have s3_6_2 : 0 < a := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) s3_6_1)
      -- 3.6.3. restate 3.4
      have s3_6_3 : 1 = a * k := by exact s3_4.symm
      -- 3.6.4. def:divides d := a, n := 1, from 3.6.3
      have s3_6_4 : a ∣ (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := (1 : ℤ)))).mpr ⟨k, s3_6_3⟩
      -- 3.6.5. inspection
      have s3_6_5 : (1 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
      -- 3.6.6. substitute
      have c1 : 1 = a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) s3_6_2 s3_6_4).symm
      have row1 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => t ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ))) c1 s3_6_5; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    · skip
      -- 3.6.7. inequalities
      have s3_6_7 : -a > 0 := by parley_order
      -- 3.6.8. mun:pos-int-nat m := −a, from 3.6.7
      have s3_6_8 : 0 < -a := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) s3_6_7)
      -- 3.6.9. algebra, from 3.4
      have s3_6_9 : 1 = -a * -k := by linear_combination (norm := parley_norm) (-1) * s3_4
      -- 3.6.10. def:divides d := −a, n := 1, from 3.6.9
      have s3_6_10 : -a ∣ (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := -a) (n := (1 : ℤ)))).mpr ⟨-k, s3_6_9⟩
      -- 3.6.11. mun:divides-one d := −a, from 3.6.8, 3.6.10
      have s3_6_11 : -a = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := -a) s3_6_8 s3_6_10)
      -- 3.6.12. inspection
      have s3_6_12 : (-1 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
      -- 3.6.13. substitute
      have c1 : -1 = a := by linear_combination (norm := parley_norm) s3_6_11
      have row1 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => t ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ))) c1 s3_6_12; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1

end Parley.Proofs.Hammack.SquareDividesItself.SquareDividesItself
