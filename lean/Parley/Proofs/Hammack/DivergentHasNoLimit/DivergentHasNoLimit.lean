module

public import ArithTactics
public import OrderTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/divergent-has-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivergentHasNoLimit.DivergentHasNoLimit

set_option maxHeartbeats 400000 in
theorem divergent_has_no_limit (a : ℤ → ℝ) (hH2 : ∀ M : ℝ, ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n > N → a n > M)) :
    ¬ (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds L)) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain L from S
  obtain ⟨L, s1⟩ := hS
  -- 2. def:tends-to, from 1
  have s2 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp s1
  -- 3. instantiate ε := 1 in line 2
  have r22_1 : (0 : ℤ) < 1 := by parley_arith
  have s3 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < 1) := by first | exact (s2 (1 : ℝ) (by parley_side)) | exact ((s2 (1 : ℝ) (by parley_side))).symm | simpa using (s2 (1 : ℝ) (by parley_side)) | exact_mod_cast (s2 (1 : ℝ) (by parley_side)) | (have h := (s2 (1 : ℝ) (by parley_side)); parley_rat_of_real h) | (have h := (s2 (1 : ℝ) (by parley_side)); parley_side)
  -- 4. obtain P from line 3
  obtain ⟨P, s4a, s4b⟩ := s3
  -- 5. instantiate M := L + 1 in H2
  have s5 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n > N → a n > L + 1) := by first | exact (hH2 (L + 1)) | exact ((hH2 (L + 1))).symm | simpa using (hH2 (L + 1)) | exact_mod_cast (hH2 (L + 1)) | (have h := (hH2 (L + 1)); parley_side)
  -- 6. obtain Q from line 5
  obtain ⟨Q, s6a, s6b⟩ := s5
  -- 7. inequalities, from 6
  have s7 : Q > 0 := by parley_order
  -- 8. inequalities
  have s8 : P + Q ≥ P := by parley_order
  -- 9. inequalities, from 4
  have s9 : P > 0 := by parley_order
  -- 10. inequalities
  have s10 : P + Q > Q := by parley_order
  -- 11. instantiate n := P + Q in line 4, from 8
  have s11 : abs (a (P + Q) - L) < 1 := by first | linarith [(s4b (P + Q) (by parley_side) (by parley_side))] | (have h := (s4b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s4b (P + Q) (by parley_side) (by parley_side)) | (have h := (s4b (P + Q) (by parley_side) (by parley_side)); parley_side)
  -- 12. instantiate n := P + Q in line 6, from 10
  have s12 : a (P + Q) > L + 1 := by first | linarith [(s6b (P + Q) (by parley_side) (by parley_side))] | (have h := (s6b (P + Q) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s6b (P + Q) (by parley_side) (by parley_side)) | (have h := (s6b (P + Q) (by parley_side) (by parley_side)); parley_side)
  -- 13. mun:abs-difference-lt x := a(P + Q), c := L, δ := 1, from 11
  have s13 : L - 1 < a (P + Q) ∧ a (P + Q) < L + 1 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (P + Q)) (c := L) (δ := (1 : ℝ)))).mp s11
  -- 14. inequalities
  have s14 : a (P + Q) ≤ L + 1 := by parley_order
  -- 15. inequalities, from 14
  have s15 : ¬ a (P + Q) > L + 1 := by parley_side
  exact s15 s12

end Parley.Proofs.Hammack.DivergentHasNoLimit.DivergentHasNoLimit
