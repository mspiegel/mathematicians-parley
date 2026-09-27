# Pilot: the Schröder–Bernstein theorem

Theorem 14 of `SELECTION.md`, set.mm's `sbth`, Metamath 100 #25:

  if A goes one-to-one into B and B goes one-to-one into A, then there is a
  bijection from A to B.

The proof is the fixed-point one, not the chain argument. The chain argument
follows each point back through f and g as far as it goes, and that needs a
set defined by recursion, which the corpus does not have (Theorem 16 is
chosen for recursion). The fixed-point proof needs only one set, built at
once: the largest part C of A with nothing of g's image of what f misses on C
landing in C. On C the bijection is f, off C it is the way back along g.

---

## Theorems fixed-part and schroeder-bernstein

The proof is `proof/schroeder-bernstein.proof`, two theorems. `fixed-part`
finds C, and is set.mm's `sbthlem3` said as "there is such a part".
`schroeder-bernstein` defines the bijection by cases and shows it is one.
Both elaborate, to `elaboration/proof/schroeder-bernstein/fixed-part.mm` and
`schroeder-bernstein.mm`, assume nothing, and verify.

Numbers: `fixed-part` has 36 numbered steps and `schroeder-bernstein` 78.
The second is long because one-to-one takes four cases and onto two, each
of which reads the value of h in its case.

---

## Rendered view

Let A and B be sets, f : A → B and g : B → A, both one-to-one.

For a part X of A, M(X) = g[B ∖ f[X]]: take what f misses from X, and see
where g sends it. D is the parts X of A that share nothing with M(X), and C
is everything in at least one of them.

**Lemma (fixed-part).** There is C ⊆ A with g[B ∖ f[C]] = A ∖ C.

*Proof.* M reverses inclusion. Every member X of D has M(C) ⊆ M(X), and
M(X) shares nothing with X, so M(C) shares nothing with X; hence nothing of
M(C) is in C, and M(C) ⊆ A ∖ C. Then C ⊆ A ∖ M(C), so M(A ∖ M(C)) ⊆ M(C),
which shares nothing with A ∖ M(C). That puts A ∖ M(C) in D and so inside
C, which is A ∖ C ⊆ M(C).

**Theorem.** There is a bijection from A to B.

*Proof.* Take C from the lemma, R = f[C], and

  h(x) = f(x) if x ∈ C, g⁻¹(x) otherwise, for x ∈ A.

Off C, x is in A ∖ C = M(C), so x = g(y) for some y ∈ B outside R, and
h(x) = g⁻¹(g(y)) = y. So h(x) ∈ B ∖ R and g(h(x)) = x. On C, h(x) = f(x) ∈ R.
So a point on C and a point off C never meet under h, and h is one-to-one:
on C by f, off C by g, across by R. Every b ∈ B is reached: in R, from the
x ∈ C with f(x) = b; outside R, from g(b), which is off C. ∎

---

## Decisions made with the reader

- **The image is `f[X]`**, set.mm's `f " X`, defined in words as
  {f(x) : x ∈ X}. The first draft spelt it out, and the statement nested one
  spelt-out image inside another; a reader decoded it from the inside.
  `f(X)` was rejected because M(C) beside f(C) would put applying a function
  and taking an image side by side under one notation.
- **The union of a family is `⋃(X ∈ D) X`**, a new notation row
  (`indexed-union`, set.mm's `ciun`).
- **One-to-one is `f : A → B is one-to-one`**, the arrow every function is
  written with and the property after it (`one-to-one`, `wf1`).
- **A function by cases is written as the brace prints it**, one case to a
  line with `if` and a last `otherwise` (`by-cases`, `cif`); `SYNTAX.md`
  has the rule.
- **The inverse is `g⁻¹`** (`inverse`, `ccnv`), used only where g is
  one-to-one.
- **A part of A is `X ⊆ A`**, never X ∈ 𝒫A: `there is C ⊆ A with`,
  `for every X ⊆ A`, `{X ⊆ A : …}`, `let X ⊆ A` and `for X ⊆ A` on a
  define each build the power-set formula, so the page has no 𝒫.
- **D's condition is M(X) ∩ X = ∅**, read "shares nothing with", where the
  first draft wrote M(X) ⊆ A ∖ X and left the reader to see a disjointness
  in a complement.
- **The lemma carries a `note`, and each define a plain reading**, so the
  meaning stands beside each formula before a reader decodes it.

---

## What the pilot reveals

1. **A property in a `let` line was never asked for.** The first draft
   wrote `let g : Y → X is one-to-one`. That fitted the function form with
   "X is one-to-one" read as the set g maps into, and a function's type is
   a declaration no citation is asked for, so the item's one-to-one-ness
   passed unchecked: the checker called the line that supplied it surplus.
   A reader cannot see that difference, so the fault was the language's.
   The line is now written as a textbook writes it, `let g : Y → X be
   one-to-one`, and what `be` says is asked for as a membership is; the
   plain function form refuses anything after its arrow that is not a set.
2. **"Onto" is still not a word.** `thm:stdlib/functions/onto-bijection`
   says every point is reached, as Cantor's finding 6 asked, and set.mm's
   `dffo3` reads that as onto below the page.
3. **A value of h is read off the brace by citing the define.** No
   justification head could cite a define, and a calculation link cites
   one line, so "t ∉ C, so by the definition of h, h(t) = g⁻¹(t)" had no
   form. A reader points at the brace they can see, so a define's label
   became a head: `h(t) = g⁻¹(t)` is justified `D2, from 4.1`, the line
   saying t ∉ C and t ∈ A. `SYNTAX.md` and `GRAMMAR.md` say so.
4. **h : A → B is shown from its values.** `thm:stdlib/functions/function-into`
   says a function whose every value lies in Y maps into Y; set.mm says it
   of a map (`fmpt`), and a defined function is one.
5. **A define's letters met themselves.** M's rule binds two letters, D's
   condition holds M's rule written out, and C is a union over D. So M read
   at C written out is a map over a domain that binds the map's own
   letter. The kernel's lemmas for maps hold their letter apart from the
   domain and the scope entirely, bound or not, and the first elaboration
   of the lemma failed to verify on exactly that. The elaborator now reads
   a rule at such a value in a second spelling of its letters, fixed once
   per map (`rule_apart`), and puts a value it had to write out back as the
   line writes it where written out it would meet a binder (`refolded`).
6. **The letters nearly ran out.** The lemma fixes seven capitals, each
   taking a set variable, and the defines, binders and obtained names take
   more; the first attempt at item 5, which took two fresh letters for every
   value, exhausted all 26. The second spelling of a rule takes its letters
   only while nothing holds them.
7. **The checker reads a fact as written as well as expanded.** An item
   whose function letter the claim fills with h (`h : A → B`) asks for h(s)
   as written, and the facts had only the rule of h at s.
8. **An `obtain` from an item that asks for nothing takes no `from`.**
   `fixed-part` is cited with only its `let` lines, which are never asked,
   so the production now makes `, from` optional as it is for `def:` and
   `thm:`.
9. **The statement is about functions, not dominance.** set.mm's `sbth`
   says A ≼ B and B ≼ A give A ≈ B. The page says the injections those
   mean, which is what a reader is given, and the `metamath` line points at
   `sbth`.
