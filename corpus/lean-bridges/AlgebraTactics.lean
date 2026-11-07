module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Parser.Command
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.Basic
public import Tactics
public import NormTactics

/-!
# What an `algebra` step leaves to the ring and field tactics

`parley_ring` closes an identity of `algebra` with no line cited, and
`parley_field` what `linear_combination` asks of one that divides; each
clears the divisions with `parley_clear` when `ring1` alone does not close
it. A generated file imports this module only when it calls one of them.
-/

public section

open Lean Meta Elab Tactic in
/-- For each line `0 < x`, the line `x ≠ 0`: an integer the page puts in ℕ,
the q of p/q, is not 0, which is what clearing a division by it asks. -/
elab "parley_pos_ne" : tactic => withMainContext do
  let lines := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for line in lines do
    let said ← instantiateMVars line.type
    unless said.isAppOfArity ``LT.lt 4 do continue
    unless (said.getArg! 2).isAppOfArity ``OfNat.ofNat 3 do continue
    try
      let proof ← mkAppM ``ne_of_gt #[mkFVar line.fvarId]
      let ty ← inferType proof
      liftMetaTactic fun g => do
        let g' ← g.assert `h_ne ty proof
        let (_, g'') ← g'.intro1P
        return [g'']
    catch _ => pure ()

/-- What `field_simp` asks of a divisor cast up, `(q : ℂ) ≠ 0`: a line, or
one of the integer itself with the cast moved (`parley_pos_ne`). -/
macro "parley_cast_ne" : tactic =>
  `(tactic| first | assumption | (norm_cast; done) | (exact_mod_cast ‹_›) | (norm_cast; omega))

/-- Clears what an `algebra` step divides by, from the lines saying each
divisor is not 0, a product, a quotient or a negation not 0 taken as each
of its parts not 0. A natural number above 0, the q of p/q, is not 0. -/
macro "parley_clear" : tactic =>
  `(tactic| ((try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or,
      pow_eq_zero_iff, Nat.pos_iff_ne_zero] at *) <;> (try cases_type* And) <;> field_simp))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
macro "parley_ring" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A power to an exponent the page puts in ℕ₀, `x ^ e.toNat`, its
    -- `toNat` taken apart by the facts in scope (`parley_norm`).
    | (simp (disch := omega) only [Int.toNat_add, Int.toNat_mul, Int.reduceToNat,
        mul_one, one_mul]; (try push_cast); ring1; done)
    | (simp (disch := omega) only [Int.toNat_add, Int.toNat_mul, Int.reduceToNat,
        mul_one, one_mul]; done)
    -- A factorial divided by itself, which is not 0, where the file's
    -- modules tag the factorial into `parley_unfold`.
    | (field_simp [parley_unfold]; done)
    | (simp only [inv_inv, one_div, div_div, div_pow] <;> ring1; done)
    | (parley_clear <;> ring1; done)
    | (parley_clear; done)
    -- Divisions by integers the page puts in ℕ, p/q − r/s: each divisor
    -- not 0 by its fact 0 < q.
    | (parley_pos_ne; field_simp (disch := parley_cast_ne); done)
    | (parley_pos_ne; field_simp (disch := parley_cast_ne); ring1; done)
    -- A sum read as linear (METHODS.md): each side gathered into one sum
    -- over the range, its factors free of the index taken inside, and the
    -- summands compared index by index.
    | (simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring1; done))

theorem parley_pow_three {M : Type*} [Monoid M] (a : M) : a ^ 3 = a ^ 2 * a := by
  rw [pow_succ]

theorem parley_pow_four {M : Type*} [Monoid M] (a : M) : a ^ 4 = (a ^ 2) ^ 2 := by
  rw [← pow_mul]

/-- A square root of a real number not negative, squared in ℂ, is the number. -/
theorem parley_ofReal_sqrt_sq {x : ℝ} (h : 0 ≤ x) : ((Real.sqrt x : ℝ) : ℂ) ^ 2 = (x : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt h]

open Lean Meta Elab Tactic in
/-- A term not 0 by a line that says a term equal to it is not 0, √3·i − 1
of −1 + i·√3 ≠ 0: `field_simp` writes a divisor in its own order, which a
line need not share. Each such line is tried, and the two terms shown equal
by `linear_combination`. -/
elab "parley_ne_zero" : tactic => withMainContext do
  let lines := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for line in lines do
    let said ← instantiateMVars line.type
    unless said.isAppOfArity ``Not 1 do continue
    let saved ← saveState
    try
      evalTactic (← `(tactic| ((try rw [ne_eq]); intro h)))
      setGoals (← (← getMainGoal).apply (mkFVar line.fvarId))
      evalTactic (← `(tactic| linear_combination h))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    saved.restore
  throwError "parley_ne_zero: no line says the term is not 0"

/-- What `field_simp` asks of a divisor: not 0, by a line, by arithmetic, or
part by part of a product, a power or a quotient. -/
syntax "parley_nz" : tactic
macro_rules
  | `(tactic| parley_nz) => `(tactic| first
    | assumption
    | (norm_num1; done)
    | parley_ne_zero
    | (apply mul_ne_zero <;> parley_nz)
    | (apply pow_ne_zero; parley_nz)
    | (apply div_ne_zero <;> parley_nz))

/-- An identity over ℂ of i and square roots, which the step divides by
terms of them, −1 + i√3: i² = −1 and (√x)² = x put in, the divisions the
lines show are by terms not 0 cleared, a divisor of i and square roots
alone taken to its conjugate over its norm, a real number, and the powers
of i and of the roots that are left put in again. -/
macro "parley_radical" : tactic =>
  `(tactic| ((simp (disch := positivity) only [mul_pow, Complex.I_sq, Complex.I_mul_I, parley_ofReal_sqrt_sq] at *); (try push_cast at *); (try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or] at *); (try cases_type* And); field_simp (disch := parley_nz); (try simp (disch := positivity) only [div_eq_mul_inv, Complex.inv_def, map_sub, map_add, map_neg, map_one, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Real.mul_self_sqrt]); push_cast; ring_nf; simp (disch := positivity) only [parley_pow_three, parley_pow_four, Complex.I_sq, parley_ofReal_sqrt_sq]; push_cast; ring1))

/-- What `linear_combination` asks once the cited equations are subtracted,
where the step divides: zero, once the divisions are cleared. -/
macro "parley_field" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A divisor said not 0 in its own least type, 3 * (n : ℤ) - 1 ≠ 0, and
    -- divided by in ℝ, written the other way round, ↑n * 3 - 1: the facts
    -- cast up and both normalised, field_simp sees they are one.
    | ((try rify at *); ring_nf at *; field_simp; ring1; done)
    -- Divisors field_simp does not clear, 3n − 1 beside a fact that says it
    -- is not 0: the fractions are joined and multiplied out one at a time,
    -- each divisor shown not 0 from the facts.
    | ((try push_cast at *); (try rify at *);
        simp (disch := simp_all) only [div_add_div, div_sub_div, div_eq_div_iff, eq_div_iff,
          div_eq_iff, mul_one_div, mul_div_assoc', div_mul_eq_mul_div, div_add', add_div',
          div_sub', sub_div']; ring1; done)
    | (parley_clear <;> ring1; done)
    -- A divisor of integers cast up, (k : ℂ) + 1 of k ∈ ℕ₀: not 0 by the
    -- facts of the integers, the cast moved (`parley_cast_ne`).
    | (field_simp (disch := parley_cast_ne); ring1; done)
    | (parley_radical; done))

end
