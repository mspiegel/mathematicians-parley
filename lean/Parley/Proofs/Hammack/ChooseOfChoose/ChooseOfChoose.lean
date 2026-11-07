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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/choose-of-choose.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseOfChoose.ChooseOfChoose

set_option maxHeartbeats 600000 in
theorem choose_of_choose (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : c ≤ b) (hH5 : b ≤ a) :
    (LeanBridges.Counting.choose a b : ℤ) * (LeanBridges.Counting.choose b c : ℤ) = (LeanBridges.Counting.choose a (b - c) : ℤ) * (LeanBridges.Counting.choose (a - b + c) c : ℤ) := by
  -- 1. inequalities, from H2
  have s1 : 0 ≤ b := by parley_order
  -- 2. def:range-between k := b, a := 0, b := a, from H5, 1
  have s2 : b ∈ Finset.Icc (0 : ℤ) a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := b) (a := (0 : ℤ)) (b := a))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := b) (a := (0 : ℤ)) (b := a))).mpr (by parley_side); parley_side)
  -- 3. def:C n := a, k := b, from 2
  have s3 : (LeanBridges.Counting.choose a b : ℚ) = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial b : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b)) (by parley_side); parley_side)
  -- 4. inequalities, from H3
  have s4 : 0 ≤ c := by parley_order
  -- 5. def:range-between k := c, a := 0, from H4, 4
  have s5 : c ∈ Finset.Icc (0 : ℤ) b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := c) (a := (0 : ℤ)) (b := b))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := c) (a := (0 : ℤ)) (b := b))).mpr (by parley_side); parley_side)
  -- 6. def:C n := b, k := c, from 5
  have s6 : (LeanBridges.Counting.choose b c : ℚ) = (LeanBridges.Counting.factorial b : ℚ) / ((LeanBridges.Counting.factorial (b - c) : ℚ) * (LeanBridges.Counting.factorial c : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := b) (by parley_side) (k := c)) (by parley_side); parley_side)
  -- 7. inequalities
  have s7 : 0 ≤ b - c := by parley_order
  -- 8. inequalities
  have s8 : -c ≤ 0 := by parley_order
  -- 9. inequalities, from H5, 8
  have s9 : b - c ≤ a := by parley_order
  -- 10. def:range-between k := b − c, a := 0, b := a, from 7, 9
  have s10 : b - c ∈ Finset.Icc (0 : ℤ) a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := b - c) (a := (0 : ℤ)) (b := a))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := b - c) (a := (0 : ℤ)) (b := a))).mpr (by parley_side); parley_side)
  -- 11. def:C n := a, k := b − c, from 10
  have s11 : (LeanBridges.Counting.choose a (b - c) : ℚ) = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - (b - c)) : ℚ) * (LeanBridges.Counting.factorial (b - c) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a) (by parley_side) (k := b - c)) (by parley_side); parley_side)
  -- 12. substitute
  have s12 : (LeanBridges.Counting.choose a (b - c) : ℚ) = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b + c) : ℚ) * (LeanBridges.Counting.factorial (b - c) : ℚ)) := by
    have c1 : a - (b - c) = a - b + c := by parley_ring
    have c1_w : (a : ℚ) - ((b : ℚ) - (c : ℚ)) = (a : ℚ) - (b : ℚ) + (c : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (LeanBridges.Counting.choose a (b - c) : ℚ) = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b + c) : ℚ) * (LeanBridges.Counting.factorial (b - c) : ℚ)) := by first | parley_put_at c1_w s11 | parley_put_at c1 s11 | parley_subst_at c1_w s11 | parley_subst_at c1 s11
    exact row1
  -- 13. inequalities
  have s13 : 0 ≤ a - b := by parley_order
  -- 14. inequalities, from 4, 13
  have s14 : 0 ≤ a - b + c := by parley_order
  -- 15. inequalities
  have s15 : c ≤ a - b + c := by parley_order
  -- 16. def:range-between k := c, a := 0, b := a − b + c, from 4, 15
  have s16 : c ∈ Finset.Icc (0 : ℤ) (a - b + c) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := c) (a := (0 : ℤ)) (b := a - b + c))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := c) (a := (0 : ℤ)) (b := a - b + c))).mpr (by parley_side); parley_side)
  -- 17. mun:nat0-as-int
  have r77_1 : 0 ≤ a - b + c := by parley_side
  have s17 : 0 ≤ a - b + c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := a - b + c))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := a - b + c))).mpr (by parley_side); parley_side)
  -- 18. def:C n := a − b + c, k := c, from 16
  have r81_1 : 0 ≤ a - b + c := by parley_side
  have s18 : (LeanBridges.Counting.choose (a - b + c) c : ℚ) = (LeanBridges.Counting.factorial (a - b + c) : ℚ) / ((LeanBridges.Counting.factorial (a - b + c - c) : ℚ) * (LeanBridges.Counting.factorial c : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := a - b + c) (by parley_side) (k := c)) (by parley_side); parley_side)
  -- 19. substitute
  have s19 : (LeanBridges.Counting.choose (a - b + c) c : ℚ) = (LeanBridges.Counting.factorial (a - b + c) : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial c : ℚ)) := by
    have c1 : a - b + c - c = a - b := by parley_ring
    have c1_w : (a : ℚ) - (b : ℚ) + (c : ℚ) - (c : ℚ) = (a : ℚ) - (b : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (LeanBridges.Counting.choose (a - b + c) c : ℚ) = (LeanBridges.Counting.factorial (a - b + c) : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial c : ℚ)) := by first | parley_put_at c1_w s18 | parley_put_at c1 s18 | parley_subst_at c1_w s18 | parley_subst_at c1 s18
    exact row1
  -- 20. mun:nat0-as-int
  have r90_1 : 0 ≤ a - b := by parley_side
  have s20 : 0 ≤ a - b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := a - b))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := a - b))).mpr (by parley_side); parley_side)
  -- 21. mun:nat0-as-int
  have r94_1 : 0 ≤ b - c := by parley_side
  have s21 : 0 ≤ b - c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := b - c))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := b - c))).mpr (by parley_side); parley_side)
  -- 22. mun:factorial-nat n := a − b, from 20
  have s22 : 0 < (LeanBridges.Counting.factorial (a - b) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := a - b) (by parley_side))
  -- 23. mun:factorial-nat n := b − c, from 21
  have s23 : 0 < (LeanBridges.Counting.factorial (b - c) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := b - c) (by parley_side))
  -- 24. mun:factorial-nat n := a − b + c, from 17
  have s24 : 0 < (LeanBridges.Counting.factorial (a - b + c) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := a - b + c) (by parley_side))
  -- 25. calculation
  have s25 : (LeanBridges.Counting.choose a b : ℤ) * (LeanBridges.Counting.choose b c : ℤ) = (LeanBridges.Counting.choose a (b - c) : ℤ) * (LeanBridges.Counting.choose (a - b + c) c : ℤ) := by
    try qify
    calc (LeanBridges.Counting.choose a b : ℚ) * (LeanBridges.Counting.choose b c : ℚ) = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial b : ℚ)) * (LeanBridges.Counting.choose b c : ℚ) := by parley_subst s3
      _ = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial b : ℚ)) * ((LeanBridges.Counting.factorial b : ℚ) / ((LeanBridges.Counting.factorial (b - c) : ℚ) * (LeanBridges.Counting.factorial c : ℚ))) := by parley_subst s6
      _ = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b + c) : ℚ) * (LeanBridges.Counting.factorial (b - c) : ℚ)) * ((LeanBridges.Counting.factorial (a - b + c) : ℚ) / ((LeanBridges.Counting.factorial (a - b) : ℚ) * (LeanBridges.Counting.factorial c : ℚ))) := by parley_ring
      _ = (LeanBridges.Counting.factorial a : ℚ) / ((LeanBridges.Counting.factorial (a - b + c) : ℚ) * (LeanBridges.Counting.factorial (b - c) : ℚ)) * (LeanBridges.Counting.choose (a - b + c) c : ℚ) := by parley_subst s19
      _ = (LeanBridges.Counting.choose a (b - c) : ℚ) * (LeanBridges.Counting.choose (a - b + c) c : ℚ) := by parley_subst s12
  all_goals exact s25

end Parley.Proofs.Hammack.ChooseOfChoose.ChooseOfChoose
