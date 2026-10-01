# Pilot: De Moivre's formula

Theorem 18 of `SELECTION.md`, set.mm's `demoivre`, Wiedijk #17:

  for every real x and every n ∈ ℕ₀, (cos x + i·sin x)ⁿ = cos(nx) + i·sin(nx).

The proof is the textbook induction on n with the angle-addition formulas,
which `SELECTION.md` planned. ProofWiki's page proves a form with a modulus
r, from n = 1, through the product of complex numbers in polar form, so it
was not taken as the source. set.mm proves the formula another way, through
the exponential function and for every complex x and integer n; its
statement covers this one, and the elaborated proof is the corpus's own.

---

## Theorem de-moivre

The proof is `proofs/de-moivre.proof`, one theorem. It elaborates to
`corpus/elaboration/proofs/de-moivre/de-moivre.mm`, assumes nothing, and
verifies.

Numbers: 30 numbered steps, 6 of them at the top. Steps 1 to 5 say what is
real and complex and that i·i = −1; 6 is the induction, its base 6.1 to 6.9
and its step 6.10 with fourteen steps inside.

---

## Rendered view

Let x ∈ ℝ and n ∈ ℕ₀.

**Theorem.** (cos x + i·sin x)ⁿ = cos(nx) + i·sin(nx).

*Proof.* By induction on n.

At n = 0 the left side is 1, and the right side is cos 0 + i·sin 0 =
1 + i·0 = 1.

Suppose the formula holds at k. Then

  (cos x + i·sin x)^(k+1) = (cos x + i·sin x)^k·(cos x + i·sin x)
    = (cos kx + i·sin kx)(cos x + i·sin x)
    = cos kx·cos x + i·(sin kx·cos x + cos kx·sin x) + i·i·sin kx·sin x
    = (cos kx·cos x − sin kx·sin x) + i·(sin kx·cos x + cos kx·sin x),

since i·i = −1, and by the angle-addition formulas this is
cos(kx + x) + i·sin(kx + x) = cos((k + 1)x) + i·sin((k + 1)x). ∎

---

## Decisions made with the reader

1. **ℂ and i are on the page.** ℂ is kept off the page only in plane
   geometry, where a point is not to read as a complex number
   (`GEOMETRY.md`). Here ℂ is one of the number systems a line may name,
   and i is a constant.
2. **cos and sin are library functions, written cos(x) and sin(x),** as
   gcd(a, b) is: a formula applies a function with brackets.
3. **cos, sin and i are mundane definitions.** A reader of De Moivre's
   formula knows cos and sin from school, and set.mm's definition by the
   exponential is not what that reader means by them, so they state only
   what they build, as min and max do. i is i·i = −1.
4. **The angle-addition formulas are named theorems,** `cos-add` and
   `sin-add`, as a textbook names them. cos 0 = 1, sin 0 = 0, that cos and
   sin are real at a real, and i ∈ ℂ are mundane.
5. **x ∈ ℝ,** as a textbook states it, where set.mm allows any complex x.
6. **The exponent laws hold over ℂ.** `exponent-step` and `exponent-zero`
   are stated for a complex base, as set.mm states them, rather than a real
   one beside a complex copy.

---

## What the pilot reveals

1. **ℂ was a notation away.** The tables that put one number system inside
   another already ran to ℂ (`rules::WITHIN`). Only the checker skipped it,
   reading what a membership implies, because "x ∈ ℂ" could not be written;
   with ℂ a notation it no longer does, and a line saying 2 ∈ ℝ answers an
   item asking 2 ∈ ℂ.
2. **`algebra` does not rewrite by i·i = −1.** It decides ring and field
   identities and replaces a name by the value a cited line gives it, and
   i·i is no name. So the step multiplies out with i·i left standing, a
   `substitute` puts −1 for it, and `algebra` tidies the rest: three steps
   where a textbook writes one line, each a move the textbook makes.
3. **Rewriting inside a term is a step of its own.** A calculation link
   cites a line saying that link, so cos(kx + x) is put for its expansion by
   a `substitute` step, and the chain cites that step.

---

## Status

Checker clean, elaborated with nothing assumed, verified.
