module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/prime-two-or-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeTwoOrOdd.PrimeTwoOrOdd

set_option maxHeartbeats 400000 in
theorem prime_two_or_odd (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) :
    (P = 2 ∨ Odd P) := by
  -- 1. mun:even-or-odd n := P
  have s1 : Even P ∨ Odd P := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := P))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. obtain k: def:even n := P, from C1
    obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := P))).mp hC1
    -- 2.2. def:divides d := 2, n := P, from 2.1
    have s2_2 : (2 : ℤ) ∣ P := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := P))).mpr ⟨k, s2_1⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := P))).mpr ⟨k, s2_1⟩; parley_side)
    -- 2.3. def:prime p := P, from H2
    have s2_3 : ∀ d : ℤ, 0 < d → d ∣ P → d = 1 ∨ d = P := (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp hH2).2
    -- 2.4. instantiate d := 2 in line 2.3
    have s2_4 : (2 : ℤ) ∣ P → (2 : ℤ) = 1 ∨ 2 = P := by first | exact (s2_3 (2 : ℤ) (by parley_side)) | exact ((s2_3 (2 : ℤ) (by parley_side))).symm | simpa using (s2_3 (2 : ℤ) (by parley_side)) | exact_mod_cast (s2_3 (2 : ℤ) (by parley_side)) | (have h := (s2_3 (2 : ℤ) (by parley_side)); parley_side)
    -- 2.5. mun:modus-ponens, from 2.2, 2.4
    have s2_5 : (2 : ℤ) = 1 ∨ 2 = P := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ P) (Q := (2 : ℤ) = 1 ∨ 2 = P) s2_4 s2_2)
    -- 2.6. cases, from 2.5
    have s2_6 : 2 = P := by
      rcases s2_5 with hC3 | hC4
      · skip
        -- 2.6.1. arithmetic
        have s2_6_1 : (2 : ℤ) ≠ 1 := by parley_arith
        exact absurd hC3 s2_6_1
      · skip
        exact hC4
    -- 2.7. restate 2.6
    have s2_7 : P = 2 := by parley_side
    -- 2.8. mun:or-left P := P = 2, Q := P is odd, from 2.7
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := P = 2) (Q := Odd P) s2_7)
  · skip
    -- 2.9. mun:or-right P := P = 2, Q := P is odd, from C2
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := P = 2) (Q := Odd P) hC2)

end Parley.Proofs.Setmm.PrimeTwoOrOdd.PrimeTwoOrOdd
