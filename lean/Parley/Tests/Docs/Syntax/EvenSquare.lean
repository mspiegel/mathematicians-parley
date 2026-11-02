module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare

/-! Written from tests/docs/syntax.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Syntax.EvenSquare

theorem even_square (n : ℤ) (hH2 : Even (n ^ 2)) :
    Even n := by
  -- 1. contradiction
  have s1 : ¬ Odd n := by
    by_contra hc_hS
    have hS : Odd n := by parley_suppose hc_hS
    -- 1.1. thm:odd-square, from S
    have s1_1 : Odd (n ^ 2) := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare.odd_square (n := n) (by parley_side)); parley_side)
    -- 1.2. mun:not-both n := n², from H2
    have s1_2 : ¬ Odd (n ^ 2) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := n ^ 2) (by parley_side)); parley_side)
    all_goals parley_side
  -- 2. mun:even-or-odd
  have s2 : Even n ∨ Odd n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n)); parley_side)
  -- 3. mun:disjunctive-syllogism P := n is even, Q := n is odd, from 1, 2
  have s3 : Even n := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even n) (Q := Odd n) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Docs.Syntax.EvenSquare
