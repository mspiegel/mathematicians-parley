# Pilot: Königsberg bridges

Theorem 29 of `SELECTION.md`, set.mm's `konigsberg`, Wiedijk #54:

  the multigraph of Königsberg's four land masses and seven bridges has no
  walk that crosses every bridge exactly once.

The argument is Euler's, as ProofWiki gives it: a walk that crosses every
edge once arrives at and leaves every vertex but its two ends by a pair of
edges each time it passes through, so every other vertex has even degree,
and at most two have odd degree; in Königsberg all four do. set.mm proves it
through `konigsberglem1`–`5` and its theorem on Euler paths.

---

## Theorems

The proof is `proofs/konigsberg.proof`, four theorems of 48 numbered steps,
87 with those inside blocks. All four elaborate to
`corpus/elaboration/proofs/konigsberg/`, assume nothing, and verify. Each is
proved before a theorem citing it.

- `degree-by-walk`: if e : {1, …, n} → E lists every edge exactly once, the
  degree of a vertex x is the number of places i where e(i) is incident with
  x.
- `walk-parity`: in an Euler path of n edges, a vertex that is neither the
  start nor the end has even degree. Euler's argument.
- `odd-vertices`: a traversable graph has at most two vertices of odd
  degree.
- `konigsberg`: the graph of Königsberg is not traversable. Its `let` line
  gives the graph whole: its four vertices, its seven edges, and which two
  vertices each edge joins.

---

## Rendered view

**Lemma (degree-by-walk).** Let e : {1, …, n} → E be one-to-one and onto the
edges, and x a vertex. Then deg(x) = |{i ∈ {1, …, n} : x is incident with
e(i)}|.

*Proof.* i ↦ e(i) takes the places where e(i) is incident with x one to one
onto the edges incident with x, so the two sets have the same size. ∎

**Lemma (walk-parity).** Let v : {0, …, n} → V and e : {1, …, n} → E form an
Euler path, and x a vertex other than v(0) and v(n). Then deg(x) is even.

*Proof.* e(i) is incident with x exactly when x = v(i − 1) or x = v(i), and
not both, since an edge joins two distinct vertices. So deg(x) = d + r,
where d counts the departures from x, the i with x = v(i − 1), and r the
arrivals, the i with x = v(i). Since x is not v(0), d counts the i from 1 to
n − 1 with x = v(i); since x is not v(n), so does r. So d = r = m, and
deg(x) = 2m. ∎

**Lemma (odd-vertices).** A traversable graph has at most two vertices of
odd degree.

*Proof.* Take an Euler path v, e. By walk-parity a vertex of odd degree is
v(0) or v(n), so there are at most two. ∎

**Theorem (konigsberg).** The graph of Königsberg is not traversable.

*Proof.* The degrees are deg(A) = 5 and deg(B) = deg(C) = deg(D) = 3, read
off the edges. All four are odd, and by odd-vertices a traversable graph
has at most two. ∎

---

## Decisions made with the reader

1. **The graph is given whole in a `let` line,** its vertices and edges
   listed and each edge's two ends named, as a textbook draws it.
2. **"x is incident with a",** the term graph theory defines, for a vertex
   being an end of an edge; "is an end of" read as too long, and "meets"
   was set aside. The notation record says what it means.
3. **An Euler path counts its edges from 1, as a walk does.** set.mm counts
   from 0; the shift is proved once in the library (`gtravsh`, `gtravxfr`),
   and the page never renumbers.
4. **walk-parity names the departures and arrivals,** d and r, by defines
   with `reads` lines, so its steps read as Euler's argument does.
5. **A degree is read off the graph in one step by `inspection`,** from the
   degree said once of every vertex and the graph's `let` line; so is the
   count of the vertices of odd degree.
6. **Dull facts are written where they are needed** (`READERS.md`): a count
   being in ℕ₀ is a requires line of the step that rests on it, not a step.
7. **Each theorem comes before a theorem citing it,** and each define where
   it is first used.
8. **The note of degree-by-walk** says what the theorem counts in the
   reader's words.

---

## What the pilot reveals

1. **A graph library,** `graphs.records` and `graphs.proved`: a multigraph's
   `let` line, "joins", "is incident with", deg, "form a walk", "form an
   Euler path" and traversable, with counting over a range in
   `counts.proved`.
2. **`inspection` works out each side of a claim and compares them:** a
   listed set, a set-builder over one, its size, a closed numeral, or a term
   a cited "for all" equation over a listed set gives at an element.
   `tests/elaborator/inspection.proof` writes each kind of claim it decides.
3. **The language grew:** `fix` became `proof`, a block that may open with an
   assumption alone; a define may stand in a theorem's header; an induction
   may run over the k with k ≤ n; a contradiction may end "…, which is
   impossible".
4. **The tools refused some thirty-five correct steps,** each a fault met for
   the first time in the middle of the argument, and each fixed in the tool:
   rule tables missing lemmas; letters bound in a define's body matched
   letter for letter (`fit_read`, `same`); a define that could not name a
   product; a requires line kept only where a line below wrote its term
   (`built_on`); a proof's files included in the order it cited them rather
   than the order they rest on one another (`rested_first`); ∅ read as a
   number by `inspection`; and others in reading citations, hypotheses and
   facts. This is why a pilot bringing what no proof writes now has it
   tested first (`SELECTION.md`).
5. **One fault only Metamath saw:** citing odd-vertices left a set-builder's
   letter unfilled, which the elaborator accepted and the verifier refused.
