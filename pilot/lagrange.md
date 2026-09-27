# Pilot: Lagrange's theorem

Theorem 15 of `SELECTION.md`, set.mm's `lagsubg`, Metamath 100 #71:

  in a finite group, the number of elements of a subgroup divides the
  number of elements of the group.

The proof is the textbook one: the cosets of H split G into parts, each part
has as many elements as H, so |G| is |H| times the number of parts.

---

## Theorem lagrange

The proof is `proof/lagrange.proof`, one theorem. It elaborates to
`elaboration/proof/lagrange/lagrange.mm`, assumes nothing, and verifies.

Numbers: 109 numbered steps, 22 of them at the top. Blocks 4 to 8 are the
coset facts (gH lies in G, g is in gH, a coset is fixed by any of its
members), block 9 is the bijection from H to gH, and 10 to 22 count.

---

## Rendered view

Let G be a finite group with operation · and identity e, and H a subgroup
of G. For g ∈ G, gH is {g·h : h ∈ H}. K is the set of cosets: the parts of G
of the form aH.

**Theorem.** |H| divides |G|.

*Proof.* H ⊆ G, so H is finite. Every coset gH lies in G, by closure, and
contains g, since g = g·e with e ∈ H.

If x ∈ aH, say x = a·h, then xH ⊆ aH, since x·c = a·(h·c) with h·c ∈ H; and
a ∈ xH, since a = x·h⁻¹. So aH ⊆ xH as well, and xH = aH: a coset is the
coset of each of its members.

For g ∈ G, t(c) = g·c sends H into gH, is one-to-one by cancellation, and
reaches every member of gH. So |gH| = |H|.

The cosets make up G, since each lies in G and each g ∈ G is in gH. Two that
share a point x are both xH, so they are equal. Each has |H| elements, so
|G| = |K| · |H|, and |H| divides |G|. ∎

---

## Decisions made with the reader

- **A group is let with its parts named**: `let G be a finite group with
  operation · and identity e`. G is the set of its elements, which is what a
  reader means by G, and set.mm's structure W with its `Base` and `+g` is
  never written.
- **H is a subgroup by an `assume`**, `assume H is a subgroup of G`, which
  introduces H as a `let` would.
- **The statement keeps "finite" in the `let` line** and says `|H| divides
  |G|`.
- **A coset is `gH`** and an inverse `g⁻¹`, as a school text writes them.
- **`·` is the one operation symbol.** A proof about a group written with
  `+` or `∘` would need the operation to be a name the `let` line gives; that
  is left until a theorem asks for it.
- **The whole argument is on the page**, with counting by parts a general
  library item (`thm:stdlib/counting/partition-count`) rather than set.mm's
  index, which is built from the relation of being in one coset.

---

## What the pilot reveals

1. **A group is a structure set.mm names and a reader does not.** The
   group's `let` line gives G, e and the operation their terms, and the
   notations that need the group's operation, inverse, subgroups or cosets
   name them by a word beginning `@` in their `target`, filled from that
   line (`db/notation.records`). A proof that lets no group and writes `a·b`
   of group elements is a defect, reported where it is written.
2. **Letters take the sort of what they range over.** `for every g ∈ G,
   g ∈ gH` has no `let` for g; the sentence says what g ranges over, and G
   holds group elements, so g is one. Without that, `k·m` with neither sort
   known was ambiguous between numbers and a group. A group element's hole
   now takes nothing of unknown sort, so an undeclared product stays a
   product of numbers.
3. **Two letters side by side became a notation once.** `gH` is the one
   place two bare names are joined, and only a group element beside a set
   of them; `GRAMMAR.md` says why `and` is still a word.
4. **A set of sets says what it holds.** `for every Y ∈ K, |Y| = m` was
   ambiguous between absolute value and size, because K was only `a set`.
   The kinds already knew K's members are sets, and a set whose members are
   sets now has the sort `set-of-sets`, so a letter in it is a set.
5. **The letters ran out.** The proof spells fifteen lowercase letters and
   fixes some twenty names in its blocks, and set.mm has 26 lettered
   setvars. The spare list now ends with set.mm's primed setvars, a′ and the
   rest, which no reader writes and which no other proof reaches.
6. **Three counting lemmas were proved below the page**, in
   `elaboration/stdlib/proved.mm`: counting by equal parts (`gpartcnt`),
   a set of parts of a finite set being finite (`gpartsfin`), and a
   bijection from a finite set giving equal sizes (`gcardeq`, since this
   set.mm's `hashen` asks both sets finite). `gpartcnt`'s hypotheses each
   bind letters of their own, and the elaborator binds a deduction's open
   letters from the lines the step cites for them.
7. **`grplcan` names its operation only where the step supplies it.** Its
   conclusion is `X = Y`, so nothing fixed `.+` before its naming
   hypothesis was asked. A naming hypothesis now fixes its variable where
   the term it names is known, and a bare `Z ∈ B` is matched after what says
   more of Z, so the equation `g·s = g·r`, not the first member of G to
   hand, says what Z is.
8. **A definition whose right side is an existence was read only from a
   witness.** `g ∈ ⋃(Y ∈ K) Y` from the line `there is Y ∈ K with g ∈ Y` is
   the definition read right to left, as any other is; it now is. And a
   witness may come from the line putting it in the domain, where the body
   is a term equal to itself: `there is a ∈ G with gH = aH` from g ∈ G.
9. **An inner quantifier's domain may name the outer letter.** Instantiating
   `for every a ∈ G, for every x ∈ aH, …` at a := b changes the inner domain
   and body together, which `raleqbidv` carries.
10. **The subgroup line is a sort line.** A step may rest on it without
    citing it, as on a `let`; a lemma asking that H be a set finds it there.
11. **Bound letters bind once across an item's hypotheses.** The union and
    the two `for every` lines cited for partition-count are all written over
    Y.
12. **A claim may bind its own letter where it reads a definition.** Step
    15.3 says `there is b ∈ G with Z = bH` where K's define binds a. The
    checker compared the two letter for letter, so the step first had to
    say `there is a ∈ G with Z = aH` just after 15.2 had made a one
    particular element, and obtain the element as b. It now compares a
    definition's formula with a claim up to the letters each binds.
13. **A definition read at a term keeps its letter apart from the term's.**
    K is `{X ⊆ G : there is g ∈ G with X = gH}`, as a textbook writes the
    cosets. Read at gH, the checker put gH in for X and let K's g catch the
    g of gH, which said `there is g ∈ G with gH = gH`; so K first bound a.
    The checker now spells the bound letter afresh where a value would be
    caught, and step 12.2's `there is a ∈ G with gH = aH` is the reading.
    The same comparison let the √2 proof say `there is r ∈ ℤ with p = 2r`
    where it said k and obtained r.

---

## Status

Checker clean, elaborated with nothing assumed, verified. Every other
elaborated file is unchanged. The planted defects include a group line
without its identity, a coset read without H ⊆ G, parts counted without
saying they do not overlap, and a coset member with no line naming what it
is the element times.
