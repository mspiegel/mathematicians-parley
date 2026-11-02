module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/divisor-of-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower

theorem divisor_of_power (K : ℤ) (M : ℤ) (n : ℕ) (hH3 : 0 < n) (hH4 : K ∣ M) :
    K ∣ M ^ n := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℕ, 0 < m → K ∣ M ^ m := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 1.1. restate H4
      have s1_1 : K ∣ M ^ 1 := by parley_side
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. mun:divides-multiple e := K, a := M^m, x := M, from IH
      have s1_2 : K ∣ M ^ m * M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m) (x := M) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m) (x := M) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m) (x := M) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m) (x := M) (by parley_side))
      -- 1.3. substitute
      have s1_3 : K ∣ M ^ (m + 1) := by
        have c1 : M ^ m * M = M ^ (m + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m)); qify; linear_combination (norm := parley_norm) h)
        have row1 : K ∣ M ^ (m + 1) := by parley_subst_at c1 s1_2
        exact row1
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : K ∣ M ^ n := by first | exact (s1 n (by parley_side)) | exact ((s1 n (by parley_side))).symm | simpa using (s1 n (by parley_side)) | exact_mod_cast (s1 n (by parley_side))
  all_goals parley_side

end Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower
