module

public import Mathlib
public import ArithTactics
public import Roots

/-!
# Real arithmetic of √, π, ln, exp, sin and cos

What a page's `real arithmetic` decides: √8 = 2·√2, ln(8) = 3·ln(2),
ln(2) ≠ 0, cos(π/2) = 0, e < π. `parley_real` tries `parley_arith` first,
which decides the rest of real arithmetic, and then the ways below, each
from Mathlib's values and laws of these functions. A generated file that
calls it imports this module alone of the tactics beside `Tactics`
(`build::lean`), so a change here rebuilds only those files.
-/

public section

/-- Real arithmetic, `parley_arith` and then the ways of √, π, ln, exp, sin
and cos. -/
macro "parley_real" : tactic =>
  `(tactic| first
    | parley_arith
    | (positivity; done)
    | (norm_num; done)
    -- Values Mathlib names, and the laws of √, ln and exp.
    | (simp only [Real.log_one, Real.log_exp, Real.exp_log, Real.exp_zero, Real.log_zero,
        Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two,
        Real.sin_pi_div_two, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_three,
        Real.sin_pi_div_six, Real.cos_pi_div_six, Real.sin_pi_div_three,
        Real.mul_self_sqrt, Real.sqrt_mul_self, Real.sq_sqrt, Real.sqrt_sq, Real.exp_add,
        Real.cos_two_pi, Real.sin_two_pi]; norm_num; done)
    | (norm_num [Real.sqrt_eq_iff_mul_self_eq, Real.sq_sqrt, Real.sqrt_sq, Real.mul_self_sqrt]; done)
    -- A value worked out to a whole numeral said to be one, √4 ∈ ℕ as
    -- `∃ m : ℤ, 0 < m ∧ ↑m = √4`: that numeral the witness.
    | (norm_num [Real.sqrt_eq_iff_mul_self_eq, Real.sq_sqrt, Real.sqrt_sq, Real.mul_self_sqrt];
        first | (refine ⟨_, ?_, Int.cast_ofNat _⟩; norm_num; done) | (exact ⟨_, Int.cast_ofNat _⟩))
    -- ln of a power, a product or a quotient: ln(8) = 3·ln(2) is ln(2³).
    | (rw [← Real.log_rpow (by norm_num)]; norm_num; done)
    | (rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num; done)
    | (rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num; done)
    -- √a = t of t not negative: t·t = a, alone or as one side of a sum.
    | (rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]; ring_nf;
       norm_num [Real.sq_sqrt]; done)
    | (congr 1; rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]; ring_nf;
       norm_num [Real.sq_sqrt]; done)
    | (norm_num [sub_ne_zero, Real.sqrt_eq_one, Real.sin_pi_div_four, Real.cos_pi_div_four,
        div_lt_one, Real.sqrt_lt', Real.lt_sqrt]; done)
    -- ln compared: ln 3 < ln 4 = 2·ln 2, ln 2 ≠ ln 3.
    | (rw [← Real.log_rpow (by norm_num)]; exact Real.log_lt_log (by norm_num) (by norm_num); done)
    | (exact (Real.log_lt_log (by norm_num) (by norm_num)).ne; done)
    | (exact (Real.log_lt_log (by norm_num) (by norm_num)).ne'; done)
    | (rw [one_div, Real.log_inv]; done)
    -- exp of ln, and of a sum.
    | (rw [Real.exp_log (by norm_num)]; done)
    | (rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_one_pow]; norm_num; ring_nf; done)
    -- ln of a number above 1 is positive, so not 0.
    | (exact Real.log_pos (by norm_num); done)
    | (exact (Real.log_pos (by norm_num)).ne'; done)
    | (exact Real.log_lt_log (by norm_num) (by norm_num); done)
    -- A difference of logarithms above 0: one logarithm below the other,
    -- either as written or of a power, 2·ln 2 = ln 4.
    | (rw [gt_iff_lt, sub_pos];
       first
         | exact Real.log_lt_log (by norm_num) (by norm_num)
         | (rw [← Real.log_rpow (by norm_num)]; exact Real.log_lt_log (by norm_num) (by norm_num));
       done)
    -- A number below a logarithm, 1 < ln 3: e¹ below the number.
    | (rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9;
       norm_num at *; linarith; done)
    -- sin² + cos² at any angle.
    | (exact Real.sin_sq_add_cos_sq _; done)
    | (exact Real.cos_sq_add_sin_sq _; done)
    -- Roots in a sum, a product or a power: multiplied out, each √a·√a
    -- put as a; and a value of sine or cosine first where there is one.
    | (simp only [Real.sin_pi_div_four, Real.cos_pi_div_four, Real.sin_pi_div_six,
        Real.cos_pi_div_six, Real.sin_pi_div_three, Real.cos_pi_div_three];
       ring_nf; norm_num [Real.sq_sqrt]; done)
    | (ring_nf; (try norm_num [Real.sq_sqrt, pow_succ]); (try ring_nf); done)
    -- A quotient of roots, √12/√3, is the root of the quotient.
    | (rw [← Real.sqrt_div (by norm_num)]; norm_num;
       (try rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]); norm_num; done)
    -- A quotient with a root below, 1/(√3 − 1): the denominators cleared.
    | (rw [div_eq_div_iff (by norm_num [sub_ne_zero, Real.sqrt_eq_one]) (by norm_num)];
       ring_nf; norm_num [Real.sq_sqrt]; done)
    -- A sine or cosine at a multiple of π beyond the first quadrant, put
    -- there first (`Roots`): sin(9π/4) = sin(π/4).
    | (parley_angles; (try norm_num); done)
    -- Roots in one form on each side, or an order of them (`Roots`).
    | parley_roots
    | parley_roots_order
    -- A whole number that a root is, or that none is: √4 = 2, √2/√8 = 1/2.
    | (parley_roots_split; norm_num; (try simp only [← Nat.cast_ofNat (R := ℝ), Nat.cast_inj]);
       (try norm_num); done)
    | (parley_roots_split; field_simp; rintro ⟨m, hm⟩; norm_cast at hm; omega)
    -- π², through π < 3.15.
    | (have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith; done)
    -- Bounds Mathlib gives of e, π and ln 2.
    | (have := Real.pi_gt_three; have := Real.pi_lt_d2; have := Real.exp_one_lt_d9;
       have := Real.exp_one_gt_d9; have := Real.log_two_lt_d9; have := Real.log_two_gt_d9;
       norm_num at *; linarith; done))

/-- A line in ℝ of rationals, a "for all ε ∈ ℝ" taken at ε = 1/2, read in ℚ,
where the claim is written in its own type: each rational term cast down,
under any binder, `exact_mod_cast` reaching none there. -/
macro "parley_rat_of_real " h:ident : tactic =>
  `(tactic| (simp only [← Rat.cast_natCast (α := ℝ), ← Rat.cast_intCast (α := ℝ),
      ← Rat.cast_one (α := ℝ), ← Rat.cast_ofNat (α := ℝ), ← Rat.cast_div, ← Rat.cast_sub,
      ← Rat.cast_add, ← Rat.cast_mul, ← Rat.cast_abs, ← Rat.cast_neg, ← Rat.cast_pow,
      ← Rat.cast_zpow, ← Rat.cast_sum, Rat.cast_lt, Rat.cast_le, Rat.cast_inj] at $h:ident; first
                | exact $h:ident
                | (linear_combination (norm := parley_norm) $h:ident; done)
                | (linear_combination (norm := parley_norm) -$h:ident; done)
                -- An item's natural exponent given an integer's `toNat`,
                -- read at the claim's integer power.
                | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Nat.cast_one,
                    Int.toNat_of_nonneg] at $h:ident ⊢; first
                      | (linear_combination (norm := parley_norm) $h:ident; done)
                      | (linear_combination (norm := parley_norm) -$h:ident; done))))
