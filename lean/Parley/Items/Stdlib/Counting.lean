module

public import Parley.Library

/-! Written from corpus/stdlib/counting.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Counting

theorem def_factorial_1 :
    (Nat.factorial 0 : ℤ) = 1 :=
  by simp

theorem def_factorial_2 :
    (Nat.factorial 1 : ℤ) = 1 :=
  by simp

theorem def_factorial_3 (n : ℕ) :
    (Nat.factorial (n + 1) : ℤ) = (Nat.factorial n : ℤ) * ((n : ℤ) + 1) :=
  by push_cast [Nat.factorial_succ]; ring

end Parley.Items.Stdlib.Counting
