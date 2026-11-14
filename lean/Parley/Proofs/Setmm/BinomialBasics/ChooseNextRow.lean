module

public import Counting
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow

theorem choose_next_row (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose (N + 1) N : ℤ) = N + 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ N := by linarith only [hH1]
  have s1b : N ≤ N + 1 := by linarith
  -- 2. def:range-between k := N, a := 0, b := N + 1, from 1
  have s2 : N ∈ Finset.Icc (0 : ℤ) (N + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N + 1))).mpr ⟨s1a, s1b⟩
  -- 3. algebra
  have s3 : N + 1 - N = 1 := by ring1
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = 1 := by
    calc (LeanBridges.Counting.factorial (N + 1 - N) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s3; push_cast at h ⊢; exact_mod_cast h)
      _ = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
  -- 5. def:factorial n := N
  have s5 : (LeanBridges.Counting.factorial (N + 1) : ℤ) = (LeanBridges.Counting.factorial N : ℤ) * (N + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := N) hH1)
  -- 6. calculation
  qify
  calc (LeanBridges.Counting.choose (N + 1) N : ℚ) = (LeanBridges.Counting.factorial (N + 1) : ℚ) / ((LeanBridges.Counting.factorial (N + 1 - N) : ℚ) * (LeanBridges.Counting.factorial N : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := N + 1) (add_nonneg (hH1) (by norm_num)) (k := N)) s2
    _ = (LeanBridges.Counting.factorial (N + 1) : ℚ) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
        have e_w : (LeanBridges.Counting.factorial (N + 1 - N) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℚ => (LeanBridges.Counting.factorial (N + 1) : ℚ) / (t * (LeanBridges.Counting.factorial N : ℚ))) e_w
    _ = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
        have e_w : (LeanBridges.Counting.factorial (N + 1) : ℚ) = (LeanBridges.Counting.factorial N : ℚ) * ((N : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s5; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℚ => t / (1 * (LeanBridges.Counting.factorial N : ℚ))) e_w
    _ = (N : ℚ) + 1 := by have hz1 : (LeanBridges.Counting.factorial N : ℚ) ≠ 0 := (by positivity); field

end Parley.Proofs.Setmm.BinomialBasics.ChooseNextRow
