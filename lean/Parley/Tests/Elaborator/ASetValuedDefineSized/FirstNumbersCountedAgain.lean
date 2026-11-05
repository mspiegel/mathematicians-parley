module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted

/-! Written from tests/elaborator/a-set-valued-define-sized.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCountedAgain

theorem first_numbers_counted_again (m : ℕ) :
    ((Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ).ncard : ℤ) = (m : ℤ) := by
  -- 1. thm:first-numbers-counted
  have s1 : ((Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ).ncard : ℤ) = (m : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)) | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)) | exact_mod_cast ((Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m))).symm | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCounted.first_numbers_counted (m := m)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ASetValuedDefineSized.FirstNumbersCountedAgain
