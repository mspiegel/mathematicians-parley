module

public import Mathlib
public import Tactics

/-!
# An item over ℂ read at real numbers

`parley_of_complex h` reads in ℝ an equation an item over ℂ gives at real
numbers. A generated file imports this module only when it calls it.
-/

public section

/-- An equation `h` an item over ℂ gives of real numbers, exp(a + 1) =
exp(a)·exp(1) of exp-sum at a real a: read in ℝ, each complex exp, sin and
cos of a real cast the real one. -/
macro "parley_of_complex " h:ident : tactic =>
  `(tactic| (simp only [← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, ← Complex.ofReal_sin, ← Complex.ofReal_cos] at $h:ident; exact_mod_cast $h:ident))

end
