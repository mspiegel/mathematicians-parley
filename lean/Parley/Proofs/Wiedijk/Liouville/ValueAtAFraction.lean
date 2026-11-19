module

public import Polynomials
public import PowerTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Polynomials

/-! Written from proofs/wiedijk/liouville.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Liouville.ValueAtAFraction

theorem value_at_a_fraction (F : ℂ → ℂ) (hH2 : F ∈ LeanBridges.Polynomials.integerPolynomials) (N : ℤ) (hH3 : 0 < N) (hH4 : (LeanBridges.Polynomials.degree F : ℤ) = N) (p : ℤ) (q : ℤ) (hH6 : 0 < q) (hH7 : F ((p : ℂ) / (q : ℂ)) ≠ 0) :
    ‖F ((p : ℂ) / (q : ℂ))‖ ≥ 1 / (q : ℝ) ^ N.toNat := by
  -- 1. thm:integer-polynomial-at-a-fraction, from H2
  have s1 : ∃ m : ℤ, (m : ℂ) = (q : ℂ) ^ LeanBridges.Polynomials.degree F * F ((p : ℂ) / (q : ℂ)) := by exact (Parley.Items.Stdlib.Polynomials.thm_integer_polynomial_at_a_fraction (F := F) hH2 (p := p) (q := q) hH6)
  -- 2. substitute deg(F) = N (H4) into line 1
  have s2 : ∃ m : ℤ, (m : ℂ) = (q : ℂ) ^ N.toNat * F ((p : ℂ) / (q : ℂ)) := by
    have e_nat : LeanBridges.Polynomials.degree F = (N).toNat := by (have h := hH4; omega)
    exact Eq.subst (motive := (fun t : ℕ => ∃ m : ℤ, (m : ℂ) = (q : ℂ) ^ t * F ((p : ℂ) / (q : ℂ)))) e_nat s1
  -- 3. mun:integer-polynomial-real x := p/q, from H2
  have s3 : ∃ m : ℝ, (m : ℂ) = F ((p : ℂ) / (q : ℂ)) := by
    have hI : ∃ m : ℝ, (m : ℂ) = F ((p : ℂ) / (q : ℂ)) := by (have h := ((Parley.Items.Stdlib.Polynomials.mun_integer_polynomial_real (F := F) hH2 (x := (p : ℝ) / (q : ℝ)))); push_cast at h ⊢; exact h)
    exact hI
  -- 4. mun:power-positive a := q, m := N
  have r195_1 : q > 0 := by linarith only [hH6]
  have s4 : q ^ N.toNat > 0 := by (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (q : ℚ)) (m := N) (by exact_mod_cast gt_iff_lt.mp r195_1)); simp only [parley_zpow_toNat (n := N) (h := le_of_lt hH3)] at h ⊢; exact_mod_cast h)
  -- 5. mun:product-nonzero x := q^N, y := F(p/q), from H7, 3
  have r199_1 : q ^ N.toNat ≠ 0 := ne_of_gt (by linarith only [s4])
  have s5 : (q : ℂ) ^ N.toNat * F ((p : ℂ) / (q : ℂ)) ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := (q : ℂ) ^ N.toNat) (y := F ((p : ℂ) / (q : ℂ))) (by exact_mod_cast r199_1) hH7)
  -- 6. mun:nonzero-integer-abs z := q^N·F(p/q), from 2, 5
  have s6 : ‖(q : ℂ) ^ N.toNat * F ((p : ℂ) / (q : ℂ))‖ ≥ 1 := by rw [← Classical.choose_spec s2]; rw [← Classical.choose_spec s2] at s5; norm_cast at s5; (exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonzero_integer_abs (z := (Classical.choose s2)) (by exact_mod_cast s5)))
  -- 7. mun:abs-product x := q^N, y := F(p/q), from 3
  have s7 : ‖(q : ℂ) ^ N.toNat * F ((p : ℂ) / (q : ℂ))‖ = abs ((q : ℝ) ^ N.toNat) * ‖F ((p : ℂ) / (q : ℂ))‖ := by rw [← Classical.choose_spec s3]; (exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := (q : ℝ) ^ N.toNat) (y := (Classical.choose s3))))
  -- 8. inequalities
  have s8 : q ^ N.toNat ≥ 0 := by linarith only [s4]
  -- 9. def:abs x := q^N, from 8
  have s9 : abs (q ^ N.toNat) = q ^ N.toNat := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := q ^ N.toNat)) s8
  -- 10. substitute |q^N| = q^N (line 9)
  have s10 : abs ((q : ℝ) ^ N.toNat) * ‖F ((p : ℂ) / (q : ℂ))‖ = (q : ℝ) ^ N.toNat * ‖F ((p : ℂ) / (q : ℂ))‖ := by
    have e_w : abs ((q : ℝ) ^ N.toNat) = (q : ℝ) ^ N.toNat := by have h := congrArg (fun x : ℤ => (x : ℝ)) s9; push_cast at h; linear_combination h
    exact congrArg (fun t : ℝ => t * ‖F ((p : ℂ) / (q : ℂ))‖) e_w
  -- 11. transitivity, from 10, 7, 6
  have s11 : (q : ℝ) ^ N.toNat * ‖F ((p : ℂ) / (q : ℂ))‖ ≥ 1 := by exact LE.le.trans_eq (LE.le.trans_eq s6 s7.symm.symm) s10.symm.symm
  -- 12. mun:divide-le x := 1, y := q^N·|F(p/q)|, c := q^N, from 4, 11
  have s12 : 1 / (q : ℝ) ^ N.toNat ≤ (q : ℝ) ^ N.toNat * ‖F ((p : ℂ) / (q : ℂ))‖ / (q : ℝ) ^ N.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (1 : ℝ)) (y := (q : ℝ) ^ N.toNat * ‖F ((p : ℂ) / (q : ℂ))‖) (c := (q : ℝ) ^ N.toNat) s11 (by exact_mod_cast gt_iff_lt.mp s4))
  -- 13. algebra
  have s13 : (q : ℝ) ^ N.toNat * ‖F ((p : ℂ) / (q : ℂ))‖ / (q : ℝ) ^ N.toNat = ‖F ((p : ℂ) / (q : ℂ))‖ := by have hz1 : (q : ℝ) ^ N.toNat ≠ 0 := (by positivity); field
  -- 14. transitivity, from 12, 13
  exact LE.le.trans_eq s12 s13

end Parley.Proofs.Wiedijk.Liouville.ValueAtAFraction
