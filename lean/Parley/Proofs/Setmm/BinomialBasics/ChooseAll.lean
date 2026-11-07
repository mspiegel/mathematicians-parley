module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseAll

theorem choose_all (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose N N : ℤ) = 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ N := by parley_order
  have s1b : N ≤ N := by parley_order
  -- 2. def:range-between k := N, a := 0, b := N, from 1
  have s2 : N ∈ Finset.Icc (0 : ℤ) N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N))).mpr (by parley_side); parley_side)
  -- 3. algebra
  have s3 : N - N = 0 := by parley_ring
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (N - N) : ℤ) = 1 := by
    calc (LeanBridges.Counting.factorial (N - N) : ℤ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) := by parley_subst s3
      _ = 1 := by norm_num
  -- 5. calculation
  have s5 : (LeanBridges.Counting.choose N N : ℤ) = 1 := by
    try qify
    calc (LeanBridges.Counting.choose N N : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - N) : ℚ) * (LeanBridges.Counting.factorial N : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := N) (by parley_side) (k := N)) (by parley_side); parley_side)
      _ = (LeanBridges.Counting.factorial N : ℚ) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
          have s4_w : (LeanBridges.Counting.factorial (N - N) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s4_w | parley_subst s4
      _ = 1 := by parley_ring
  all_goals exact s5

end Parley.Proofs.Setmm.BinomialBasics.ChooseAll
