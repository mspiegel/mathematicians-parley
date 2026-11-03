module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.ARealHasASign

theorem a_real_has_a_sign (x : ℝ) :
    ((x < 0 ∨ x = 0) ∨ 0 < x) := by
  -- 1. axi:trichotomy
  have s1 : (x < 0 ∨ x = 0) ∨ 0 < x := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x)); parley_side)
  all_goals exact s1

end Parley.Tests.Docs.Grammar.ARealHasASign
