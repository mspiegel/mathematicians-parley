module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/prime-divisor-in-range.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PrimeDivisorInRange.PrimeDivisorInRange

theorem prime_divisor_in_range (N : ℤ) (hH1 : 0 < N) (I : ℤ) (hH2 : I ∈ Finset.Icc (2 : ℤ) N) :
    (∃ p : ℤ, 0 < p ∧ ((Nat.Prime p.toNat ∧ p ≤ N) ∧ p ∣ I)) := by
  -- 1. mun:range-bounds a := 2, b := N, k := I, from H2
  have s1 : 2 ≤ I := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := N) (k := I) hH2)
  -- 2. mun:range-bounds a := 2, b := N, k := I, from H2
  have s2 : I ≤ N := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := N) (k := I) hH2)
  -- 3. inequalities, from 1
  have s3 : 0 < I := by parley_order
  -- 4. mun:pos-int-nat m := I, from 3
  have s4 : 0 < I := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := I) s3)
  -- 5. inequalities, from 1
  have s5 : I > 1 := by parley_order
  -- 6. obtain p: thm:prime-factor m := I, from 4, 5
  obtain ⟨p, s6a, ⟨s6b, s6c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := I) s4 s5)
  -- 7. mun:divides-le e := p, m := I, from 4, 6
  have s7 : p ≤ I := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) s6a (m := I) s4 s6c)
  -- 8. transitivity, from 7, 2
  have s8 : p ≤ N := by parley_order
  -- 9. exhibit, from 6, 8
  exact ⟨p, s6a, ⟨⟨s6b, s8⟩, s6c⟩⟩

end Parley.Proofs.Setmm.PrimeDivisorInRange.PrimeDivisorInRange
