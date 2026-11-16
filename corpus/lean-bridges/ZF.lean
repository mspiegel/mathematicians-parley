module

public import Lean.Parser.Command
public import Mathlib.SetTheory.ZFC.Class

/-!
# ZF

What "X exists" says, and the axioms of set theory that say a collection
exists, as the build writes them.

The page's sets have sorts, as Lean's do: a set of things, a set of sets of
them, and no set a member of itself. ZF has one sort, its sets, and a
collection too big to be one of them, as the collection of all sets is,
does not exist. `Sets α` says which things of a type are sets of ZF
(`IsSet`) and which set each is (`code`): every `ZFSet` is one, and a set of
things is one where each of its members is and what they are make a
`ZFSet`. An integer is a set too, as set.mm builds the numbers from sets:
each is coded by a set of its own. A statement that says a collection
exists takes its type of things with `Sets`, so that at `ZFSet` it says
what ZF says, and each letter its `let` lines introduce is a set, as
set.mm's are.
-/

public section

namespace LeanBridges.ZF

/-- The things of a type that are sets of ZF, and the set each is. -/
class Sets (α : Type*) where
  nonempty : Nonempty α
  IsSet : α → Prop
  code : α → ZFSet.{0}
  /-- Two sets with one code are one: a set is its members. -/
  code_injective : ∀ {x y : α}, IsSet x → IsSet y → code x = code y → x = y

export Sets (IsSet code code_injective)

attribute [instance] Sets.nonempty

instance : Sets ZFSet.{0} where
  nonempty := ⟨∅⟩
  IsSet _ := True
  code x := x
  code_injective _ _ e := e

/-- A set for each natural number, each apart from the others: 0 is ∅, and
n + 1 is {n}. -/
noncomputable def numeral : ℕ → ZFSet.{0}
  | 0 => ∅
  | n + 1 => {numeral n}

theorem numeral_ne_zero (n : ℕ) : numeral (n + 1) ≠ numeral 0 := by
  intro e
  have h : numeral n ∈ numeral (n + 1) := ZFSet.mem_singleton.mpr rfl
  rw [e] at h
  exact ZFSet.notMem_empty _ h

theorem numeral_injective : Function.Injective numeral := by
  intro m n e
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact absurd e.symm (numeral_ne_zero n)
  | succ m ih =>
    cases n with
    | zero => exact absurd e (numeral_ne_zero m)
    | succ n => rw [ih (ZFSet.singleton_injective e)]

/-- Each integer is a set, coded by a numeral of its own. -/
noncomputable instance : Sets ℤ where
  nonempty := ⟨0⟩
  IsSet _ := True
  code z := numeral (Denumerable.eqv ℤ z)
  code_injective _ _ e := (Denumerable.eqv ℤ).injective (numeral_injective e)

/-- The members of C are what `z` holds. -/
def Coded {α : Type*} [Sets α] (C : Set α) (z : ZFSet.{0}) : Prop :=
  ∀ y, y ∈ z ↔ ∃ c ∈ C, code c = y

open Classical in
/-- The set the members of C make, where they make one. -/
noncomputable def setCode {α : Type*} [Sets α] (C : Set α) : ZFSet.{0} :=
  if h : ∃ z, Coded C z then Classical.choose h else ∅

theorem setCode_coded {α : Type*} [Sets α] {C : Set α} (e : ∃ z, Coded C z) :
    Coded C (setCode C) := by
  unfold setCode; rw [dif_pos e]; exact Classical.choose_spec e

noncomputable instance {α : Type*} [Sets α] : Sets (Set α) where
  nonempty := ⟨∅⟩
  IsSet C := (∀ c ∈ C, IsSet c) ∧ ∃ z, Coded C z
  code C := setCode C
  code_injective {C D} hC hD e := by
    have mem : ∀ {C D : Set α}, (∀ c ∈ C, IsSet c) ∧ (∃ z, Coded C z) →
        (∀ c ∈ D, IsSet c) ∧ (∃ z, Coded D z) → setCode C = setCode D → C ⊆ D := by
      intro C D hC hD e c hc
      have : code c ∈ setCode D := e ▸ (setCode_coded hC.2 _).mpr ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hdc⟩ := (setCode_coded hD.2 _).mp this
      exact code_injective (hD.1 d hd) (hC.1 c hc) hdc ▸ hd
    exact Set.Subset.antisymm (mem hC hD e) (mem hD hC e.symm)

variable {α β : Type*} [Sets α] [Sets β]

theorem code_coded {C : Set α} (h : IsSet C) : Coded C (code C) := setCode_coded h.2

theorem mem_code {C : Set α} (h : IsSet C) {y : ZFSet.{0}} :
    y ∈ code C ↔ ∃ c ∈ C, code c = y := code_coded h y

/-- A member of a set is a set. -/
theorem member_isSet {C : Set α} (h : IsSet C) {c : α} (hc : c ∈ C) : IsSet c := h.1 c hc

theorem of_coded {C : Set α} (h : ∀ c ∈ C, IsSet c) (z : ZFSet.{0}) (hz : Coded C z) :
    IsSet C := ⟨h, z, hz⟩

/-- `axi:stdlib/sets/empty-set`. -/
theorem empty_set : IsSet (∅ : Set α) :=
  of_coded (by simp) ∅ (by intro y; simp)

/-- `axi:stdlib/sets/pairing`. -/
theorem pairing (x y : α) (hx : IsSet x) (hy : IsSet y) : IsSet ({x, y} : Set α) :=
  of_coded (by rintro c (rfl | rfl) <;> assumption) {code x, code y}
    (by intro w; simp [eq_comm])

/-- `axi:stdlib/sets/unions`. -/
theorem unions (C : Set (Set α)) (h : IsSet C) : IsSet (⋃ X ∈ C, X) := by
  refine of_coded ?_ (ZFSet.sUnion (code C)) ?_
  · intro c hc
    obtain ⟨X, hX, hcX⟩ := Set.mem_iUnion₂.mp hc
    exact member_isSet (member_isSet h hX) hcX
  · intro y
    simp only [ZFSet.mem_sUnion, mem_code h, Set.mem_iUnion₂]
    constructor
    · rintro ⟨w, ⟨X, hX, rfl⟩, hy⟩
      obtain ⟨c, hc, rfl⟩ := (mem_code (member_isSet h hX)).mp hy
      exact ⟨c, ⟨X, hX, hc⟩, rfl⟩
    · rintro ⟨c, ⟨X, hX, hc⟩, rfl⟩
      exact ⟨code X, ⟨X, hX, rfl⟩, (mem_code (member_isSet h hX)).mpr ⟨c, hc, rfl⟩⟩

/-- `axi:stdlib/sets/separation`. -/
theorem separation (X : Set α) (h : IsSet X) (P : α → Prop) : IsSet {t ∈ X | P t} := by
  classical
  refine of_coded (fun c hc => member_isSet h hc.1)
    (ZFSet.sep (fun w => ∃ c ∈ X, P c ∧ code c = w) (code X)) ?_
  intro y
  simp only [ZFSet.mem_sep, mem_code h, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, c, hc, hp, rfl⟩; exact ⟨c, ⟨hc, hp⟩, rfl⟩
  · rintro ⟨c, ⟨hc, hp⟩, rfl⟩; exact ⟨⟨c, hc, rfl⟩, c, hc, hp, rfl⟩

/-- `axi:stdlib/sets/power-sets`. -/
theorem power_sets (X : Set α) (h : IsSet X) : IsSet (𝒫 X) := by
  classical
  have sub : ∀ Y ⊆ X, IsSet Y := fun Y hY => by
    have e : {t ∈ X | t ∈ Y} = Y := Set.sep_eq_of_subset hY
    exact e ▸ separation X h (· ∈ Y)
  refine of_coded sub (ZFSet.powerset (code X)) ?_
  intro w
  rw [ZFSet.mem_powerset]
  constructor
  · intro hw
    refine ⟨{t ∈ X | code t ∈ w}, fun t ht => ht.1, ?_⟩
    ext y
    rw [mem_code (separation X h _)]
    constructor
    · rintro ⟨c, ⟨-, hc⟩, rfl⟩; exact hc
    · intro hy
      obtain ⟨c, hc, rfl⟩ := (mem_code h).mp (hw hy)
      exact ⟨c, ⟨hc, hy⟩, rfl⟩
  · rintro ⟨Y, hY, rfl⟩ y hy
    obtain ⟨c, hc, rfl⟩ := (mem_code (sub Y hY)).mp hy
    exact (mem_code h).mpr ⟨c, hY hc, rfl⟩

open Classical in
/-- `axi:stdlib/sets/replacement`. -/
theorem replacement (Y : Set α) (hY : IsSet Y) (Z : Set β) (hZ : IsSet Z) (E : α → β)
    (hE : Set.MapsTo E Y Z) : IsSet (E '' Y) := by
  let f : ZFSet.{0} → ZFSet.{0} := fun w =>
    if h : ∃ s ∈ Y, code s = w then code (E (Classical.choose h)) else ∅
  letI : ZFSet.Definable₁ f := Classical.allZFSetDefinable _
  refine of_coded ?_ (ZFSet.image f (code Y)) ?_
  · rintro _ ⟨s, hs, rfl⟩; exact member_isSet hZ (hE hs)
  · intro y
    rw [ZFSet.mem_image]
    have pick : ∀ s ∈ Y, f (code s) = code (E s) := by
      intro s hs
      have h : ∃ s' ∈ Y, code s' = code s := ⟨s, hs, rfl⟩
      simp only [f, dif_pos h]
      obtain ⟨hs', e⟩ := Classical.choose_spec h
      rw [code_injective (member_isSet hY hs') (member_isSet hY hs) e]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨s, hs, rfl⟩ := (mem_code hY).mp hw
      exact ⟨E s, ⟨s, hs, rfl⟩, (pick s hs).symm⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨code s, (mem_code hY).mpr ⟨s, hs, rfl⟩, pick s hs⟩

/-- `axi:stdlib/sets/choice`. -/
theorem choice (F : Set (Set α)) (hne : ∀ A ∈ F, A ≠ ∅) :
    ∃ g : Set α → α, Set.MapsTo g F (⋃ B ∈ F, B) ∧ ∀ A ∈ F, g A ∈ A := by
  classical
  have pick : ∀ A ∈ F, A.Nonempty := fun A hA => Set.nonempty_iff_ne_empty.mpr (hne A hA)
  refine ⟨fun A => if hA : A.Nonempty then hA.some else Classical.arbitrary _, ?_, ?_⟩
  · intro A hA
    exact Set.mem_iUnion₂.mpr
      ⟨A, hA, by simp only [dif_pos (pick A hA)]; exact (pick A hA).some_mem⟩
  · intro A hA
    simp only [dif_pos (pick A hA)]; exact (pick A hA).some_mem

/-- Every set of integers is a set: the codes of its members are among those
of all the integers, which make a set as the integers are no more than ℕ. -/
theorem integers_isSet (C : Set ℤ) : IsSet C := by
  classical
  refine of_coded (fun _ _ => trivial)
    (ZFSet.sep (fun w => ∃ c ∈ C, code c = w) (ZFSet.range (code : ℤ → ZFSet.{0}))) ?_
  intro y
  simp only [ZFSet.mem_sep, ZFSet.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, rfl⟩, c, hc, rfl⟩

/-- `axi:stdlib/sets/infinity`: ℕ, the positive integers, is a set. -/
theorem infinity : IsSet {n : ℤ | 0 < n} := integers_isSet _

/-- `mun:stdlib/sets/difference-set`. -/
theorem difference_set (X : Set α) (a : α) (h : IsSet X) : IsSet (X \ {a}) := by
  have e : {t ∈ X | t ∉ ({a} : Set α)} = X \ {a} := rfl
  exact e ▸ separation X h (· ∉ ({a} : Set α))

end LeanBridges.ZF
