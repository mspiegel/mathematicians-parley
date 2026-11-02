module

public import LeanBridges

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

theorem mun_exp_positive (x : ℝ) :
    0 < Real.exp x :=
  Real.exp_pos x

end Parley.Items.Stdlib.Logarithms
