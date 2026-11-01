module

public import Parley.Library

/-! Written from corpus/stdlib/reasoning.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Reasoning

theorem mun_or_left (P : Prop) (Q : Prop) (h1 : P) :
    P ∨ Q :=
  Or.inl h1

theorem mun_or_right (P : Prop) (Q : Prop) (h1 : Q) :
    P ∨ Q :=
  Or.inr h1

theorem mun_modus_ponens (P : Prop) (Q : Prop) (h1 : P → Q) (h2 : P) :
    Q :=
  h1 h2

end Parley.Items.Stdlib.Reasoning
