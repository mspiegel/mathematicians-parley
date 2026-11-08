module

public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/divisor-of-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower

theorem divisor_of_power (K : ℤ) (M : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : K ∣ M) :
    K ∣ M ^ n.toNat := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℤ, 0 < m → K ∣ M ^ m.toNat := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. restate H4
      have s1_1 : K ∣ M ^ 1 := by parley_side
      simpa using s1_1
    | succ m hK hIH =>
      -- 1.2. mun:divides-multiple e := K, a := M^m, x := M, from IH
      have s1_2 : K ∣ M ^ m.toNat * M := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH)
      -- 1.3. substitute
      have c1 : M ^ m.toNat * M = M ^ (m + 1).toNat := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)).symm
      have row1 : K ∣ M ^ (m + 1).toNat := by parley_subst_at c1 s1_2
      exact row1
  -- 2. instantiate m := n in line 1
  first | exact (s1 n (by parley_side)) | exact ((s1 n (by parley_side))).symm | simpa using (s1 n (by parley_side)) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)

end Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower
