module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.ChooseAll

theorem choose_all (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.choose N N : ℤ) = 1 := by
  -- 1. inequalities, from H1
  have s1a : 0 ≤ N := by linarith only [hH1]
  have s1b : N ≤ N := by linarith only []
  -- 2. def:range-between k := N, a := 0, b := N, from 1
  have s2 : N ∈ Finset.Icc (0 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := N) (a := (0 : ℤ)) (b := N))).mpr ⟨s1a, s1b⟩
  -- 3. algebra
  have s3 : N - N = 0 := by parley_ring
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (N - N) : ℤ) = 1 := by
    calc (LeanBridges.Counting.factorial (N - N) : ℤ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.factorial t : ℤ)) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 := by norm_num
  -- 5. calculation
  try qify
  calc (LeanBridges.Counting.choose N N : ℚ) = (LeanBridges.Counting.factorial N : ℚ) / ((LeanBridges.Counting.factorial (N - N) : ℚ) * (LeanBridges.Counting.factorial N : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := N) hH1 (k := N)) s2
    _ = (LeanBridges.Counting.factorial N : ℚ) / (1 * (LeanBridges.Counting.factorial N : ℚ)) := by
        have e_w : (LeanBridges.Counting.factorial (N - N) : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
        (have h := congrArg (fun t : ℚ => (LeanBridges.Counting.factorial N : ℚ) / (t * (LeanBridges.Counting.factorial N : ℚ))) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 := by parley_ring

end Parley.Proofs.Setmm.BinomialBasics.ChooseAll
