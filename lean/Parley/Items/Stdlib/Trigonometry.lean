module

public import LeanBridges

/-! Written from corpus/stdlib/trigonometry.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Trigonometry

theorem thm_cos_add (a : ℂ) (b : ℂ) :
    Complex.cos (a + b) = Complex.cos a * Complex.cos b - Complex.sin a * Complex.sin b :=
  Complex.cos_add a b

theorem thm_sin_add (a : ℂ) (b : ℂ) :
    Complex.sin (a + b) = Complex.sin a * Complex.cos b + Complex.cos a * Complex.sin b :=
  Complex.sin_add a b

theorem mun_cos_complex (a : ℂ) :
    True :=
  trivial

theorem mun_sin_complex (a : ℂ) :
    True :=
  trivial

theorem mun_cos_negative (a : ℂ) :
    Complex.cos (-a) = Complex.cos a :=
  Complex.cos_neg a

theorem mun_sin_negative (a : ℂ) :
    Complex.sin (-a) = -Complex.sin a :=
  Complex.sin_neg a

theorem mun_sin_cos_squares (a : ℂ) :
    Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 :=
  Complex.sin_sq_add_cos_sq a

end Parley.Items.Stdlib.Trigonometry
