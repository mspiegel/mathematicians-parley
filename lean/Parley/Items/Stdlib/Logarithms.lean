module

public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.Unbundled

/-! Written from corpus/stdlib/logarithms.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Logarithms

theorem mun_ln_product (x : ℝ) (y : ℝ) (h3 : 0 < x) (h4 : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul h3.ne' h4.ne'

theorem mun_ln_quotient (x : ℝ) (y : ℝ) (h3 : 0 < x) (h4 : 0 < y) :
    Real.log (x / y) = Real.log x - Real.log y :=
  Real.log_div h3.ne' h4.ne'

theorem mun_ln_power (x : ℝ) (n : ℤ) (h3 : 0 < x) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x :=
  Real.log_zpow x n

theorem mun_exp_ln (x : ℝ) (h2 : 0 < x) :
    Real.exp (Real.log x) = x :=
  Real.exp_log h2

theorem mun_ln_exp (x : ℝ) :
    Real.log (Real.exp x) = x :=
  Real.log_exp x

theorem mun_exp_sum (a : ℂ) (b : ℂ) :
    Complex.exp (a + b) = Complex.exp a * Complex.exp b :=
  Complex.exp_add a b

theorem mun_ln_order (x : ℝ) (y : ℝ) (h3 : 0 < x) (h4 : 0 < y) :
    x < y ↔ Real.log x < Real.log y :=
  (Real.log_lt_log_iff h3 h4).symm

theorem mun_ln_real (x : ℝ) (h2 : 0 < x) :
    True :=
  trivial

theorem mun_ln_nonzero (x : ℝ) (h2 : 0 < x) (h3 : x ≠ 1) :
    Real.log x ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one h2 h3

theorem mun_exp_real (x : ℝ) :
    True :=
  by (simp_all; done)

theorem mun_e_power (y : ℂ) :
    (Real.exp 1 : ℂ) ^ y = Complex.exp y :=
  by rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos 1).ne'), ← Complex.ofReal_log (Real.exp_pos 1).le, Real.log_exp]; simp

theorem mun_exp_positive (x : ℝ) :
    0 < Real.exp x :=
  Real.exp_pos x

end Parley.Items.Stdlib.Logarithms
