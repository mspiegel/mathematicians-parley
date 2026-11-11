module

public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/square-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareNotPrime.SquareNotPrime

theorem square_not_prime (A : ℤ) :
    ¬ Nat.Prime (A ^ 2).toNat := by
  -- the theorem. contradiction
  intro hS
  -- 1. mun:prime-nat p := A², from S
  have s1 : 0 < A ^ 2 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := A ^ 2) hS)
  -- 2. def:prime p := A², from S, 1
  have s2 : A ^ 2 > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) s1)).mp hS).1
  -- 3. mun:abs-square x := A
  have s3 : abs A ^ 2 = A ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A))
  -- 4. contradiction
  have s4 : abs A ≠ 0 := by
    intro hS2
    -- 4.1. substitute |A| = 0 (S2) into line 3
    have s4_1 : 0 ^ 2 = A ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 = A ^ 2)) hS2 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 4.2. inequalities
    have s4_2 : 0 ^ 2 ≥ A ^ 2 := by parley_order
    -- 4.3. inequalities, from 4.2
    have s4_3 : ¬ A ^ 2 > 1 := by parley_side
    exact s4_3 s2
  -- 5. mun:nat0-nonzero m := |A|, from 4
  have s5 : 0 < abs A := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := abs A) (by parley_side) s4)
  -- 6. algebra, from 3
  have s6 : A ^ 2 = abs A * abs A := by linear_combination (norm := parley_norm) (-1) * s3
  -- 7. def:divides d := |A|, n := A², from 6
  have s7 : abs A ∣ A ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := abs A) (n := A ^ 2))).mpr ⟨abs A, s6⟩
  -- 8. def:prime p := A², from S, 1
  have s8 : ∀ d : ℤ, 0 < d → d ∣ A ^ 2 → d = 1 ∨ d = A ^ 2 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := A ^ 2) s1)).mp hS).2
  -- 9. instantiate d := |A| in line 8, from 5
  have s9 : abs A ∣ A ^ 2 → abs A = 1 ∨ abs A = A ^ 2 := by exact (s8 (abs A) s5)
  -- 10. mun:modus-ponens, from 7, 9
  have s10 : abs A = 1 ∨ abs A = A ^ 2 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := abs A ∣ A ^ 2) (Q := abs A = 1 ∨ abs A = A ^ 2) s9 s7)
  -- 11. cases, from 10
  have s11 : abs A = 1 := by
    rcases s10 with hC1 | hC2
    · skip
      exact hC1
    · skip
      -- 11.1. transitivity, from 6, C2
      have s11_1 : abs A * abs A = 1 * abs A := by parley_side
      -- 11.2. mun:multiply-cancel a := |A|, b := 1, c := |A|, from 4, 11.1
      exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := abs A) (b := (1 : ℤ)) (c := abs A) (by parley_side) s4)
  -- 12. substitute |A| = 1 (line 11) into line 3
  have s12 : 1 ^ 2 = A ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 = A ^ 2)) s11 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 13. inequalities
  have s13 : 1 ^ 2 ≥ A ^ 2 := by parley_order
  -- 14. inequalities, from 13
  have s14 : ¬ A ^ 2 > 1 := by parley_side
  exact s14 s2

end Parley.Proofs.Setmm.SquareNotPrime.SquareNotPrime
