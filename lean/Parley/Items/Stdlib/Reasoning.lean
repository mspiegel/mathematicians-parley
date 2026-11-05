module

public import Tactics

/-! Written from corpus/stdlib/reasoning.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Reasoning

theorem axi_excluded_middle (P : Prop) :
    P ∨ ¬ P :=
  em P

theorem mun_double_negation (P : Prop) (h1 : ¬ ¬ P) :
    P :=
  not_not.mp h1

theorem mun_disjunctive_syllogism (P : Prop) (Q : Prop) (h1 : P ∨ Q) (h2 : ¬ Q) :
    P :=
  h1.resolve_right h2

theorem mun_disjunctive_syllogism_left (P : Prop) (Q : Prop) (h1 : P ∨ Q) (h2 : ¬ P) :
    Q :=
  h1.resolve_left h2

theorem mun_or_left (P : Prop) (Q : Prop) (h1 : P) :
    P ∨ Q :=
  Or.inl h1

theorem mun_or_right (P : Prop) (Q : Prop) (h1 : Q) :
    P ∨ Q :=
  Or.inr h1

theorem mun_or_swap (P : Prop) (Q : Prop) (h1 : P ∨ Q) :
    Q ∨ P :=
  by aesop

theorem mun_not_either (P : Prop) (Q : Prop) :
    ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
  not_or

theorem mun_modus_ponens (P : Prop) (Q : Prop) (h1 : P → Q) (h2 : P) :
    Q :=
  h1 h2

theorem mun_iff_both_true (P : Prop) (Q : Prop) (h1 : P) (h2 : Q) :
    P ↔ Q :=
  by (simp_all; done)

theorem mun_iff_both_false (P : Prop) (Q : Prop) (h1 : ¬ P) (h2 : ¬ Q) :
    P ↔ Q :=
  by (simp_all; done)

theorem mun_iff_from_left (P : Prop) (Q : Prop) (h1 : P ↔ Q) (h2 : P) :
    Q :=
  h1.mp h2

theorem mun_iff_from_right (P : Prop) (Q : Prop) (h1 : P ↔ Q) (h2 : Q) :
    P :=
  by (simp_all; done)

theorem mun_iff_not_from_right (P : Prop) (Q : Prop) (h1 : P ↔ Q) (h2 : ¬ Q) :
    ¬ P :=
  by exact fun hp => h2 (h1.mp hp)

end Parley.Items.Stdlib.Reasoning
