module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Lean.Parser.Command
public import ParleySimp
public import Factorials

/-!
# The tactics' ways with factorials and binomial coefficients

The factorial and the binomial coefficient, tagged into `parley_unfold`,
which `parley_norm`, `parley_ring` and `parley_arith` call `norm_num` and
`field_simp` with at the place in their lists these ways belong. Only a
file whose Lean text writes a factorial or a binomial coefficient imports
this module, so a change to `Factorials` rebuilds those files and not every
file that calls the tactics.
-/

public section

attribute [parley_unfold] LeanBridges.Counting.factorial LeanBridges.Counting.choose
  Nat.factorial Nat.factorial_ne_zero

end
