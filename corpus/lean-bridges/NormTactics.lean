module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Parser.Command
public import ParleySimp

/-!
# The check of a linear combination

`parley_norm` is the check `linear_combination` ends with in a generated
proof, `linear_combination (norm := parley_norm) e`, and in the tactic
modules that call it. It is a module of its own, apart from `parley_side`
in `Tactics`, so that a change to either rebuilds only the files that call
it.
-/

public section

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
-- The check `linear_combination` ends with: `ring1`, or `ring1` after the
-- casts are pushed in, where a function's argument is cast two ways,
-- C(↑m + 1, 1) beside C(↑(m + 1), 1), which ring1 takes as two atoms.
macro "parley_norm" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A power to an exponent the page puts in ℕ₀, written `x ^ e.toNat`:
    -- the `toNat` of a sum or product taken apart, a^(m + 1) as a^m·a, by
    -- the facts 0 ≤ m in scope, as set.mm's `expadd` takes m, n ∈ ℕ₀.
    | (simp (disch := omega) only [Int.toNat_add, Int.toNat_mul, Int.reduceToNat,
        mul_one, one_mul]; ring1; done)
    | (simp (disch := omega) only [Int.toNat_add, Int.toNat_mul, Int.reduceToNat,
        mul_one, one_mul]; push_cast; ring1; done)
    -- A function of numerals written two ways, (1 + 1)! beside 2!, where
    -- the file's modules tag the function into `parley_unfold`.
    | (norm_num [parley_unfold]; done))

end
