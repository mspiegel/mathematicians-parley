module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/factorial-plus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne

set_option maxHeartbeats 400000 in
theorem factorial_plus_one (M : ℤ) (hH1 : 0 ≤ M) (N : ℤ) (hH2 : 0 < N) (hH3 : 1 < N) (hH4 : N ≤ M) :
    ¬ (∃ m : ℤ, (m : ℚ) = ((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ)) := by
  -- the theorem. contradiction
  intro hS
  -- 1. inequalities, from H2
  have s1 : 0 < N := by parley_order
  -- 2. transitivity, from 1, H4
  have s2 : 0 < M := by parley_order
  -- 3. mun:pos-int-nat m := M, from 2
  have s3 : 0 < M := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := M) s2)
  -- 4. mun:factorial-divisible n := M, m := N, from H4, 3
  have s4 : N ∣ (LeanBridges.Counting.factorial M : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := M) (by parley_side) (m := N) (by parley_side) hH4)
  -- 5. algebra
  have s5 : (LeanBridges.Counting.factorial M : ℚ) + 1 = (N : ℚ) * (((LeanBridges.Counting.factorial M : ℚ) + 1) / (N : ℚ)) := by parley_ring
  -- 6. exhibit, from S, 5
  have s6 : ∃ k : ℤ, (LeanBridges.Counting.factorial M : ℤ) + 1 = N * k := ⟨Classical.choose hS, by have := Classical.choose_spec hS; parley_side⟩
  -- 7. def:divides d := N, n := M! + 1, from 6
  have s7 : N ∣ (LeanBridges.Counting.factorial M : ℤ) + 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := (LeanBridges.Counting.factorial M : ℤ) + 1))).mpr s6 | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := (LeanBridges.Counting.factorial M : ℤ) + 1))).mpr s6; parley_side)
  -- 8. mun:divides-difference d := N, a := M! + 1, b := M!, from 4, 7
  have s8 : N ∣ (LeanBridges.Counting.factorial M : ℤ) + 1 - (LeanBridges.Counting.factorial M : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := N) (a := (LeanBridges.Counting.factorial M : ℤ) + 1) (b := (LeanBridges.Counting.factorial M : ℤ)) s7 s4)
  -- 9. substitute
  have s9 : N ∣ (1 : ℤ) := by
    have c1 : (LeanBridges.Counting.factorial M : ℤ) + 1 - (LeanBridges.Counting.factorial M : ℤ) = 1 := by parley_ring
    have row1 : N ∣ (1 : ℤ) := by parley_subst_at c1 s8
    exact row1
  -- 10. mun:divides-one d := N, from 9
  have s10 : N = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := N) (by parley_side) s9)
  -- 11. inequalities
  have s11 : N ≠ 1 := by parley_side
  exact s11 s10

end Parley.Proofs.Setmm.FactorialPlusOne.FactorialPlusOne
