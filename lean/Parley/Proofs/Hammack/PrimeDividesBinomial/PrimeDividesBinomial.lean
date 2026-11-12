module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/prime-divides-binomial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeDividesBinomial.PrimeDividesBinomial

theorem prime_divides_binomial (p : ℤ) (hH1 : 0 < p) (k : ℤ) (hH3 : Nat.Prime p.toNat) (hH4 : 0 < k) (hH5 : k < p) :
    p ∣ (LeanBridges.Counting.choose p k : ℤ) := by
  -- 1. mun:pos-int-nat m := k, from H4
  have s1 : 0 < k := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) hH4)
  -- 2. mun:nat-minus-one n := p
  have s2 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) hH1)
  -- 3. inequalities, from 1
  have s3 : 1 ≤ k := by linarith only [s1]
  -- 4. inequalities
  have s4 : k ≤ p - 1 + 1 := by linarith only [hH5]
  -- 5. def:range-between a := 1, b := (p − 1) + 1, from 3, 4
  have s5 : k ∈ Finset.Icc (1 : ℤ) (p - 1 + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (1 : ℤ)) (b := p - 1 + 1))).mpr ⟨s3, s4⟩
  -- 6. thm:weighted-term m := p − 1, from 2, 5
  have s6 : k * (LeanBridges.Counting.choose (p - 1 + 1) k : ℤ) = (p - 1 + 1) * (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ) := by exact (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := p - 1) s2 (k := k) s5)
  -- 7. substitute
  have s7 : k * (LeanBridges.Counting.choose p k : ℤ) = p * (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ) := by
    have c1 : p - 1 + 1 = p := by parley_ring
    have row1 : k * (LeanBridges.Counting.choose p k : ℤ) = p * (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => k * (LeanBridges.Counting.choose t k : ℤ) = t * (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ))) c1 s6; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 8. mun:binomial-nat0 n := p − 1, k := k − 1, from 2
  have s8 : 0 ≤ (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := p - 1) s2 (k := k - 1))
  -- 9. mun:divides-self n := p
  have s9 : p ∣ p := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p))
  -- 10. mun:divides-multiple e := p, a := p, x := C(p − 1, k − 1), from 9
  have s10 : p ∣ p * (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := p) (x := (LeanBridges.Counting.choose (p - 1) (k - 1) : ℤ)) s9)
  -- 11. substitute k·C(p, k) = p·C(p − 1, k − 1) (line 7) into line 10
  have s11 : p ∣ k * (LeanBridges.Counting.choose p k : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => p ∣ t)) s7.symm s10; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 12. substitute
  have s12 : p ∣ (LeanBridges.Counting.choose p k : ℤ) * k := by
    have c1 : k * (LeanBridges.Counting.choose p k : ℤ) = (LeanBridges.Counting.choose p k : ℤ) * k := by parley_ring
    have row1 : p ∣ (LeanBridges.Counting.choose p k : ℤ) * k := by (have h := Eq.subst (motive := (fun t : ℤ => p ∣ t)) c1 s11; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 13. contradiction
  have s13 : ¬ p ∣ k := by
    intro hS
    -- 13.1. mun:divides-le e := p, m := k, from S, 1
    have s13_1 : p ≤ k := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := p) hH1 (m := k) s1 hS)
    -- 13.2. inequalities, from H5
    have s13_2 : ¬ p ≤ k := by linarith only [hH5]
    exact s13_2 s13_1
  -- 14. mun:prime-coprime a := k, from H3, 13
  have s14 : (Int.gcd p k : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) hH1 hH3 (a := k) s13)
  -- 15. substitute
  have s15 : (Int.gcd k p : ℤ) = 1 := by
    have c1 : (Int.gcd p k : ℤ) = (Int.gcd k p : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := k))
    have row1 : (Int.gcd k p : ℤ) = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t = 1)) c1 s14; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 16. thm:coprime-divides x := C(p, k), c := k, n := p, from 12, 15
  exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := (LeanBridges.Counting.choose p k : ℤ)) (c := k) (n := p) hH1 s12 s15)

end Parley.Proofs.Hammack.PrimeDividesBinomial.PrimeDividesBinomial
