module

public import AlgebraTactics
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
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-divides-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDividesPower.PrimeDividesPower

set_option maxHeartbeats 400000 in
theorem prime_divides_power (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (Q : ℤ) (hH3 : 0 < Q) (hH4 : Nat.Prime Q.toNat) (N : ℤ) (hH5 : 0 ≤ N) (hH6 : P ∣ Q ^ N.toNat) :
    P = Q := by
  -- 1. def:prime p := P, from H2
  have s1 : P > 1 := (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp hH2).1
  -- 2. def:prime p := Q, from H4
  have s2 : ∀ d : ℤ, 0 < d → d ∣ Q → d = 1 ∨ d = Q := (((Parley.Items.Stdlib.Divisibility.def_prime (p := Q) (by parley_side))).mp hH4).2
  -- 3. induction on m starting at 0
  have s3 : ∀ m : ℤ, 0 ≤ m → P ∣ Q ^ m.toNat → P = Q := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      intro hC1
      -- 3.1. algebra
      have s3_1 : Q ^ 0 = 1 := by parley_ring
      -- 3.2. substitute Q^0 = 1 (line 3.1) into C1
      have s3_2 : P ∣ (1 : ℤ) := by parley_subst_at s3_1 hC1
      -- 3.3. mun:divides-one d := P, from 3.2
      have s3_3 : P = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := P) (by parley_side) s3_2)
      -- 3.4. inequalities
      have s3_4 : P ≠ 1 := by parley_side
      exact absurd s3_3 s3_4
    | succ m hK hIH =>
      intro hC2
      -- 3.5. mun:exponent-step a := Q
      have s3_5 : Q ^ (m + 1).toNat = Q ^ m.toNat * Q := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := Q) (m := m) (by parley_side))
      -- 3.6. substitute Q^(m + 1) = Q^m·Q (line 3.5) into C2
      have s3_6 : P ∣ Q ^ m.toNat * Q := by parley_subst_at s3_5 hC2
      -- 3.7. thm:prime-divides-product m := Q^m, n := Q, from H2, 3.6
      have s3_7 : P ∣ Q ^ m.toNat ∨ P ∣ Q := ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := P) (by parley_side) hH2 (m := Q ^ m.toNat) (n := Q))).mp s3_6
      -- 3.8. cases, from 3.7
      rcases s3_7 with hC3 | hC4
      · skip
        -- 3.8.1. mun:modus-ponens, from C3, IH
        exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := P ∣ Q ^ m.toNat) (Q := P = Q) hIH hC3)
      · skip
        -- 3.8.2. instantiate d := P in line 2
        have s3_8_2 : P ∣ Q → P = 1 ∨ P = Q := by first | exact (s2 P (by parley_side)) | exact ((s2 P (by parley_side))).symm | simpa using (s2 P (by parley_side)) | exact_mod_cast (s2 P (by parley_side)) | (have h := (s2 P (by parley_side)); parley_side)
        -- 3.8.3. mun:modus-ponens, from C4, 3.8.2
        have s3_8_3 : P = 1 ∨ P = Q := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := P ∣ Q) (Q := P = 1 ∨ P = Q) s3_8_2 hC4)
        -- 3.8.4. cases, from 3.8.3
        rcases s3_8_3 with hC5 | hC6
        · skip
          -- 3.8.4.1. inequalities
          have s3_8_4_1 : P ≠ 1 := by parley_side
          exact absurd hC5 s3_8_4_1
        · skip
          exact hC6
  -- 4. instantiate m := N in line 3
  have s4 : P ∣ Q ^ N.toNat → P = Q := by first | exact (s3 N (by parley_side)) | exact ((s3 N (by parley_side))).symm | simpa using (s3 N (by parley_side)) | exact_mod_cast (s3 N (by parley_side)) | (have h := (s3 N (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s3 N (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s3 N (by parley_side)); parley_side)
  -- 5. mun:modus-ponens, from H6, 4
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := P ∣ Q ^ N.toNat) (Q := P = Q) s4 hH6)

end Parley.Proofs.Setmm.PrimeDividesPower.PrimeDividesPower
