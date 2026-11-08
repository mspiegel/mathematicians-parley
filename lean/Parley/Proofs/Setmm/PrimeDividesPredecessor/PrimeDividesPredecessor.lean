module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/prime-divides-predecessor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDividesPredecessor.PrimeDividesPredecessor

theorem prime_divides_predecessor (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (A : ℤ) (hH4 : P ∣ A - 1) :
    ¬ P ∣ A := by
  -- 1. def:prime p := P, from H2
  have s1 : P > 1 := (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp hH2).1
  -- 2. contradiction
  intro hS
  -- 2.1. mun:divides-difference d := P, a := A, b := A − 1, from H4, S
  have s2_1 : P ∣ A - (A - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := P) (a := A) (b := A - 1) hS hH4)
  -- 2.2. substitute
  have s2_2 : P ∣ (1 : ℤ) := by
    have c1 : A - (A - 1) = 1 := by parley_ring
    have row1 : P ∣ (1 : ℤ) := by parley_subst_at c1 s2_1
    exact row1
  -- 2.3. mun:divides-one d := P, from 2.2
  have s2_3 : P = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s2_2)
  -- 2.4. inequalities
  have s2_4 : P ≠ 1 := by parley_side
  exact s2_4 s2_3

end Parley.Proofs.Setmm.PrimeDividesPredecessor.PrimeDividesPredecessor
