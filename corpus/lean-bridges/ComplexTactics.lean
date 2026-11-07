module

public import Mathlib.Tactic.Positivity
public import Lean.Parser.Command
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Tactics

/-!
# An item over ℂ read at real numbers

`parley_of_complex h` reads in ℝ an equation an item over ℂ gives at real
numbers. A generated file imports this module only when it calls it.
-/

public section

/-- An equation `h` an item over ℂ gives of real numbers, exp(a + 1) =
exp(a)·exp(1) of exp-sum at a real a: read in ℝ, each complex exp, sin and
cos of a real cast the real one, and so each sum, product, quotient and
power of reals. A complex power of a real not below 0 is its real power
cast (`Complex.ofReal_cpow`), the fact that it is not below 0 taken from
the lines or worked out; the root of a product of P(1/n) of am-gm is one. -/
macro "parley_of_complex " h:ident : tactic =>
  `(tactic| (simp (disch := first | assumption | positivity) only [one_div,
      ← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_natCast,
      ← Complex.ofReal_intCast,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      ← Complex.ofReal_inv, ← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_prod,
      ← Complex.ofReal_cpow,
      ← Complex.ofReal_exp, ← Complex.ofReal_sin, ← Complex.ofReal_cos] at $h:ident; (try simp only [one_div]); exact_mod_cast $h:ident))

end
