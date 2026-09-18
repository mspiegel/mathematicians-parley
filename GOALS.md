# Goals

A proof system that keeps Metamath's kernel and archive format, and adds a
readable layer on top, so that the same proof text can be followed by a reader
with a high-school mathematics background or a graduate degree. The two ideas
being combined are Metamath and Guy Steele's "Growing a Language".

## What we keep from Metamath

- A very small kernel: string substitution with disjoint-variable constraints.
  No computation, no binders, no types beyond typecodes.
- No mathematical axioms in the kernel. The foundation is a library. set.mm,
  iset.mm, nf.mm and hol.mm all run on one kernel.
- Many independent verifier implementations that can be compared against each
  other, because the specification fits on a few pages.
- A standalone archive file that any verifier checks in seconds, independent of
  tool version.

## What we want to improve

Metamath is strong at archiving and verifying proofs and weak as a teaching
tool. The stored proof is a stream of lemma labels with the claims implicit, and
the granularity of a step does not match the granularity a mathematician thinks
in. We want text that a person can follow on paper, without running a tool.

We are not aiming at natural language. An LLM can translate between natural
language and whatever formal representation we choose.

## Which step count matters

Three counts are easy to confuse:

1. steps a human writes or reads
2. steps stored in the database
3. steps the kernel checks after expansion to the axioms

Only the first is the target. The kernel-checked steps can stay as large and
unreadable as they like.

Measurements on the current set.mm (September 2026, 47,812 theorems analysed):

| | median theorem | 90th percentile | 99th percentile |
|---|---|---|---|
| stored steps | 90 | 494 | 1,657 |
| essential stored steps (result typecode `\|-`) | 15 | 97 | 370 |
| syntax stored steps (build the parse tree) | 74 | 397 | 1,304 |

About 80% of stored steps are syntax steps. The median theorem has fifteen
logical steps, so step count in the stored form is not the readability problem.

Fully expanded to axioms, with every repeated subproof shared:

| theorem | stored | essential stored | distinct subproofs after expansion |
|---|---|---|---|
| id | 12 | 3 | 11 |
| pm2.21 | 7 | 2 | 35 |
| 1p1e2 (1 + 1 = 2) | 7 | 2 | 7,148,462 |

Without sharing, as a tree, 2p2e4 expands to roughly 10^33 nodes.

Of about 1.37 million essential lemma applications in set.mm, 213 labels out of
41,504 account for half. The most used are plumbing, none of which belongs in
readable text:

| label family | what it does | share of essential steps |
|---|---|---|
| adantr, adantl, ad2antrr | add an unused hypothesis | ~5% |
| syl, syl2anc, syl3anc, a1i, ax-mp | chain inferences | ~7.5% |
| oveq1d, oveq2d, oveq12d, fveq2d, fveq2, oveq1, oveq2 | rewrite inside a term | ~4.5% |
| eqid, eqtrd | reflexivity and transitivity of = | ~3.5% |
| mpbid, mpbird, sylib, sylibr | rewrite with a biconditional | ~1.7% |

The mathematical content lives in the long tail. That is what a reader should see.

## Design decisions taken so far

1. **Growth lives above the kernel.** Every construct in the readable layer has
   a specified expansion into plain kernel steps. From the kernel's point of
   view, growth is invisible. This is Steele's test: a user-added feature is
   indistinguishable from a built-in one.

2. **Declarative, not procedural.** Every step states the claim being made, in
   formula form, and names its justification. A reader can follow it without
   executing anything. Isar and Mizar are the mature examples.

3. **Hierarchical, with drill-down.** A step's justification is either a leaf
   citing lemmas or a subproof at the next level down, in the same notation.
   There is one language, Reader A's (school background), and one text,
   written at full expansion with every step justified. Reader B (graduate
   degree) reads the same text and may collapse steps in the viewer;
   collapsing is presentation only and never a property of the text. There
   is no "obvious" step anywhere in the system. The kernel sees the bottom.
   This follows Lamport's structured proofs. See `READERS.md`.

4. **Justification methods are the growable vocabulary.** "By algebra", "by
   definition of ⊆", "by induction on n", "by the previous two lines" are named
   methods defined in the database, each with a specified expansion. Adding a
   method is a library act, not a kernel change. Syntax steps are inferred and
   never appear in the text.

5. **The expansion language is total.** Expansion must terminate so that
   verification with recomputation is guaranteed to terminate. A structurally
   recursive language over parse trees, or a rewriting language whose rules are
   themselves theorems, is preferred over a Turing-complete tactic language.

6. **Elaborators are comparable, like verifiers.** Several independent
   elaborator implementations should produce verifiable, ideally byte-identical,
   expansions for the same text.

7. **Calculation blocks are a first-class form.** Equational and inequality
   chains with one justification per line cover most school and undergraduate
   mathematics, and elaborate cleanly to transitivity lemmas.

8. **Readable statements, not only readable proofs.** Hypotheses are written as
   "Let x be a set", "Assume A ⊆ B", mapping onto floating and essential
   hypotheses.

9. **Both directions, but one source per theorem.** Down: author readable text,
   elaborate to kernel steps. Up: render an existing kernel proof as a
   mechanical readable view, then a human or LLM adds the hierarchy, groupings
   and the "why". Round-tripping is not a requirement. Once a theorem has been
   enriched, the readable text is canonical and the kernel proof is derived from
   it. Unenriched theorems remain views of their .mm proof, and both states
   coexist in one database.

10. **Added context must be checkable.** Whatever a human or LLM adds must
    elaborate back to kernel steps proving the original statement. A wrong
    proposal fails to elaborate rather than entering the archive. The original
    .mm proof is the fallback.

11. **Build the up direction first.** It needs a renderer and no methods, gives
    value on all existing theorems immediately, and shows empirically which
    vocabulary to grow. The down direction then implements that vocabulary.

12. **Definitions become a checked concept.** A definitional axiom should be
    syntactically checked to introduce one new symbol and be eliminable, so
    that "by definition of" is safe and the kernel's "no axioms" property is not
    on the honour system.

13. **The first checker is disposable, and its product is evidence.** It exists
    to say what is wrong with the corpus, which steps rest on the unchecked
    closure methods, and where `SYNTAX.md` is underspecified. Those answers
    outlive the program. It is written in Python for the shortest path from the
    written grammar to something running, and it is expected to be thrown away.
    The language of the implementation that lasts is deliberately not decided
    here. Decision 6 wants several elaborators compared against a
    specification, so the one that ships is one others read and reimplement,
    and it is written against a grammar document that does not yet exist. That
    choice waits until it does, with one constraint already fixed: the
    implementation works in Unicode scalar values and UTF-16 is not used, for
    the reason given in `DATABASE.md`.

## First version

Three pieces, with the LLM outside all of them:

- a renderer for the mechanical readable view of an existing .mm proof
- an elaborator for a small initial vocabulary of justification methods
- a checker that a restructured proof still proves the original statement

## Comparison with Lean 4

Rejected on purpose:

| | Lean 4 | this project |
|---|---|---|
| kernel | dependent type theory with reduction, thousands of lines | Metamath, hundreds of lines, no computation |
| foundation | baked into the kernel | a library |
| independent checkers | a few, against a large spec | dozens, against a short spec |
| elaboration | Turing-complete, heuristic, defined by its implementation | specified, total, reimplementable |
| archive | source plus version-bound binary; hours to recheck | standalone .mm; seconds to recheck |

Must be rebuilt: definitional unfolding (free in Lean, explicit steps here);
binders (native in Lean, disjointness conditions and substitution lemmas here);
automation (simp, ring, linarith, omega, decide); input notation with
precedence, coercions and implicit arguments; structured proof commands (calc,
have, obtain, cases).

Wanted here and absent in Lean: proofs readable at rest without the info view;
two audiences served by one hierarchical text; a separation between what humans
read and what machines archive; text that teaches by itself rather than through
an interactive loop.

To copy from Lean: its macro and syntax-extension system is the most complete
realisation of Steele's essay in any prover. Take the ergonomics, not the
unspecified semantics.

## Prior work to read

- Metamath Zero and mm1 (Carneiro): separates the checked specification from
  the tactic language; infers syntax steps. Closest existing system.
- Ghilbert (Levien): modules and interfaces over Metamath databases.
- Lamport, "How to Write a 21st Century Proof": hierarchical structured proofs.
- Wenzel, Isar: declarative proof text for Isabelle.
- Mizar: readable-by-design formal mathematics and its journal.
- Lean 4: calc blocks, structured tactics, macro system.
- Dedukti and Lambdapi: a logical framework checking proofs from many systems.
- Naproche: where readable formal text shades into controlled natural language.
  Marks the boundary we stay on the formal side of.
- mmj2 worksheets and the Metamath Proof Explorer pages: the nearest existing
  readable renderings of set.mm proofs.

## Example input artifacts

We want many examples of what the readable input will look like before any
tool can check it. The Metamath library supplies the kernel-level proofs but
not the teachable proofs. Sources, grouped by which layer of the target
artifact they exemplify:

Formal and readable at rest, models for the lower level of the text:

- Mizar Mathematical Library. Declarative language designed to read like
  mathematics; each article is also published in the Journal of Formalized
  Mathematics.
- Isabelle's Archive of Formal Proofs. Isar proofs with explicit claims and
  "by" justifications. Large, mixed quality, the good entries are the target
  style.
- TLAPS examples. Hierarchical Lamport-style proofs numbered by level. The
  best model for drill-down in a real document.
- Naproche's example library. Controlled natural language, over our
  natural-language line, but shows the extreme of readable formal text.

Formal proofs designed for teaching, closest to the high-school audience:

- Macbeth, "The Mechanics of Proof". An undergraduate textbook in Lean with a
  deliberately restricted vocabulary: calculation blocks and a few named
  methods such as "by algebra". The single most relevant artifact known.
- Massot, Verbose Lean. Controlled-vocabulary proof language used to teach
  first-year students, with course material in French and English.
- Waterproof (TU Eindhoven). Coq-based environment for undergraduate analysis
  with sentence-like steps and worked examples.
- Mathematics in Lean and the Natural Number Game, for the interactive teaching
  loop rather than for text readable at rest.

Informal but structured, models for the top level and for the acceptance test:

- ProofWiki. Each step cites a named result. Informal, but structurally close
  to the declarative format.
- Hammack, "Book of Proof" (free to download) and Velleman, "How to Prove It".
- Euclid's Elements, with formalisations by Avigad, Dean and Mumma and by
  Beeson, Narboux and Wiedijk to compare against.
- Olympiad solutions and their Lean formalisations in the compfiles project,
  for rigorous proofs at the high-school level.

Cross-system comparisons, so that set.mm's version and a readable version of
the same theorem can be put side by side:

- Wiedijk, "Formalizing 100 Theorems". An index with links to formalisations in
  Metamath, Mizar, Isabelle, Lean, HOL Light and Coq.
- Wiedijk, "The Seventeen Provers of the World". The irrationality of √2 in
  seventeen systems including Metamath, with commentary.

Plan: take ten theorems from the 100-theorems list that appear in Metamath, in
Mizar or Isabelle, and in Book of Proof or ProofWiki. Collect all three
versions of each. Write the target artifact for each by hand against those
three. This produces the example corpus and the acceptance test of open
question 2 at the same time. Licences vary across these sources; check them
before copying text into the repository rather than linking.

The ten are chosen by coverage, not fame. The list is a menu, and each of
the ten should stress one thing the readable layer has to handle:

- an equational calculation chain
- an induction
- a proof by cases
- a proof by contradiction
- an existence proof with a construction
- a definition that has to be unfolded, such as divisibility or the subset
  relation
- quantifier alternation, as in a limit or the intermediate value theorem
- a set-theoretic argument, such as Cantor's theorem
- a counting argument, such as the pigeonhole principle
- one geometry theorem, because set.mm's encoding of geometry is far from
  how a school reader thinks about it

Before a candidate is chosen, its set.mm proof is checked for what the up
direction will have to hide: deduction form, class variables, set-existence
hypotheses, disjointness conditions, and its essential step count. The
Metamath 100 page lists which of the hundred set.mm proves and under which
labels. The chosen ten, with the measurements and the alternatives
considered, are in `SELECTION.md`.

All ten are written. The proof skeletons are in `proof/`, the definitions,
theorems, notation and methods they cite are in `db/`, and `DATABASE.md`
describes both formats and records what merging the ten pilots' item tables
decided. `pilot/` keeps the design commentary for each, which is the record
of why each syntax decision was taken.

## Open questions

Settled: the target is the human-facing text; both directions are wanted; a
human or LLM supplies the context that rendering cannot.

Assumed: the bottom layer is compatible with plain Metamath or Metamath Zero,
so the library is reused from what those already have, meaning set.mm or its
Metamath Zero translation. Starting a fresh database is not planned. The cost
of this assumption is that set.mm's class/set distinction, `∈ V` hypotheses,
disjointness conditions and deduction-form conventions all have to be hidden
from the high-school reader by the readable layer. That is a requirement on the
layer, not an open question.

Not yet settled, in priority order. The ordering rule: a question comes
earlier if other questions cannot be answered without it, or if changing the
answer later would invalidate work already done.

1. **Kernel.** Plain Metamath, or Metamath Zero? This is the first decision
   because it fixes the archive format, the form of the reused library, where
   syntax elision lives, and which existing verifiers apply. Metamath Zero
   already infers syntax steps and has a translation of set.mm, which is a
   point in its favour; plain Metamath has more independent verifiers and no
   parser in the kernel, which is a point in its favour.

2. **What "readable" means operationally.** The two readers and their
   acceptance tests are defined in `READERS.md`. What remains is to write
   target proofs by hand, at both levels, for two or three theorems before any
   tool is built. A candidate set is 2 + 2 = 4, the irrationality of √2, and
   one theorem with an induction. This does not depend on question 1 and can be
   done in parallel with it. Every later question is judged against these
   samples. The section "Example input artifacts" lists where to find models
   to write them against.

3. **Reading only, or also authoring, for the high-school audience.** Reading
   needs a renderer. Writing needs error messages and an interactive loop, a
   much larger system. The answer fixes the scope of the first version.

4. **The expansion language.** Its concrete design, and whether byte-identical
   output across elaborators is required or only verifiability. Can wait until
   the up direction has shown which methods are needed, but must be settled
   before any enriched proof is written, since every enriched proof depends on
   it.

5. **Notation at the input side.** Unicode or ASCII; how notation and precedence
   are declared; how a definition unfolds on demand. Needed in draft form for
   the target proofs in question 2, and finalised with question 4.

6. **Strength of the initial methods.** How much "by algebra" must do, and how
   large its expansions may be before verification time matters. The first half
   is answered. `CLOSURE.md` measures what the corpus asks of the four closure
   methods and `METHODS.md` specifies each: `inequalities` is linear arithmetic
   over an ordered field and carries the most; `algebra` is equality of
   rational expressions over a field; `arithmetic` is closed numeral facts and
   is where the dull-fact recursion stops; and `join` infers nothing at all,
   having shed its three real inferences to cited theorems. None of it needed
   the renderer. How large the expansions may be is still open and needs one of
   them written.

7. **Stability under library change.** A method's expansion refers to library
   lemmas. What happens when a lemma is renamed, generalised or removed. Must be
   settled before the enriched corpus grows, not before the first demonstration.

8. **Storage of levels.** Whether the enriched text stores every level of the
   hierarchy or lower levels are regenerated from the elaboration. An
   implementation choice that follows from questions 4 and 7.

9. **The LLM's exact role.** Which tasks it performs, how its output is
   checked, and whether the readable corpus is intended as training data. The
   architecture already keeps it outside the checked path, so the details can
   be decided last.
