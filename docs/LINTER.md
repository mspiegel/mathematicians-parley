# Lint rules

A lint rule is one that can be broken by text that parses, passes the checker,
and is correct. Nothing here is about a proof being wrong. Every rule below
records a judgement that one of two correct ways of writing the same thing is
harder to understand than the other, and suggests the easier one.

That is the division of labour, and it is uneven. The checker decides: a proof
either has the defect or it does not, and nothing is left to anyone's taste.

A linter decides nothing. It cannot tell whether a line is hard to read; it
matches the rules written here, which came from judgements people made about
particular lines, and every finding is a suggestion that a writer may take or
leave. Whether a text can be understood is settled by a reader against the
acceptance test in `READERS.md`, and no tool is party to that.

Most of this project's rules are not of that kind. `p prime` cannot be written,
because no notation has that pattern. `not n is odd` cannot be written, because
a word predicate and negation are unrelated in the precedence order. A define
with no `reads` line is reported by the checker. None of those are lint: they
are eliminated by construction or checked as defects, and nothing can produce
them to be warned about. Eliminating beats preferring, and this file is the
fallback for the cases where eliminating would cost a reading somebody wants.
Where both readings are wanted, neither can be removed, and all that is left is
to say which one a reader gets more easily.

**A linter reads the text; the checker reads the trees.** They cannot be the
same tool, because the checker is deliberately blind to the thing a linter is
for. `x ∉ B` and `not x ∈ B` build the same tree on purpose, so that a citation
offering one can satisfy an item asking for the other. By the time the checker
sees a formula, the spelling is gone. A linter has to work on the source line.

Each rule says what to write, what it replaces, why, and how many places in the
corpus are on each side today. Nothing enforces any of them yet.

## A folded negation, or the word

Four notations fold a negation into themselves, and each has a `negates` line
saying it means the same as `not` in front. Which way to write it is therefore
free, and free is what a linter is for.

| write | not | today |
|---|---|---|
| `x ∉ B` | `not x ∈ B` | 39 lines with the sign, none with the word |
| `x ≠ y` | `not x = y` | 39 lines with the sign, none with the word |
| `n is not odd` | `not (n is odd)` | 3 lines with the word, none with `not` |
| `there is no d ∈ ℤ with …` | `not there is d ∈ ℤ with …` | 2 lines with the word, none with `not` |

The sign wins for membership and equality because it is the notation a school
reader meets first and the alternative is three words. The word wins for the
other two because the alternatives need brackets, or read as "not there is",
which is not English. Each rule was settled by picking the form the corpus
mostly already used and making the rest agree.

`x ≠ y` is the sign written in a proof for what a keyboard writes `!=`. It was
long unsettled because two lines read worse with it: a doubled negation, which
the next rule removes, and the closing pair of a contradiction block, `p = 1.
not p = 1.`, which a block no longer writes, since its last step names the line
it contradicts.

## A negation proved by contradiction supposes what it denies

| write | not | today |
|---|---|---|
| `c ≠ b`, then `suppose c = b` | `c ≠ b`, then `suppose not not c = b` | 9 blocks prove a negation, all supposing what it denies |

A `contradiction` block may suppose its claim negated, or, where the claim is a
negation, the thing it denies (`METHODS.md`). For a negated claim the first
writes a doubled negation, `not not c = b`, or with the sign `not c ≠ b`,
which a reader has to undo before the argument starts, and then needs a step
citing `mun:stdlib/reasoning/double-negation` to undo it on the page. The second
says what a textbook says, "suppose c = b", and needs no step and no classical
logic. The three blocks proving a claim that is not a negation suppose its
negation, which is the only way to prove it.

### Where the universal stands

| write | not | today |
|---|---|---|
| `for all x ∈ A, f(x) ≠ B` as a claim | `f(x) ≠ B for all x ∈ A` | all 72 lines |
| `… such that f(x) ≠ B for all x ∈ A` | `… such that for all x ∈ A, f(x) ≠ B` | 9 lines |
| `… such that \|x(n) − L\| < ε for all n ≥ N` | `… such that for all n ≥ N, \|x(n) − L\| < ε` | (among the 9) |
| `… such that \|f(x) − f(c)\| < ε for all x ∈ D with \|x − c\| < δ` | `… such that for all x ∈ D, if \|x − c\| < δ then …` | (among the 9) |

A universal over one relation may be written before it or after it, and the
two are one formula. Before is the rule: it is the only form for anything
longer than one relation, and it is how a block's claim is written. After is
for the one place a textbook writes it, inside "such that", where the prefix
form would put two connectives side by side ("such that for all"). It may
carry a bound, "for all n ≥ N", or a condition of one relation, "for all
x ∈ D with |x − c| < δ", which is how a textbook writes a limit and
continuity. The nine: Cantor's statement and its last step; the
definitions of tends-to and continuity; triangular-reciprocals' step 3 and
its last step 3.4; and intermediate-value's step 15 and the two steps 16.4
and 16.25 that instantiate it. Step 3.3, and 16.5 and 16.26, which restate
an obtained universal as a claim of its own, keep the prefix form.

### Two universals over one set

| write | not | today |
|---|---|---|
| `for all s, t ∈ A, …` | `for all s ∈ A, for all t ∈ A, …` | all 12 places, 8 of them in proofs |

Where two universals in a row range over the same set, the names are listed
under one "for all", as a textbook writes "for all a, b ∈ ℝ". The two are one
formula, so a line written either way meets an item written the other, and
the rule is only about which reads better. Lagrange's "for all Y, Z ∈ K, for
all x ∈ Y ∩ Z, Y = Z" keeps its third universal apart, since x ranges over
another set.

### A bound in place of the set

| write | not | today |
|---|---|---|
| `for all ε > 0, …` where the statement says `ε ranges over ℝ` | `for all ε ∈ ℝ with ε > 0, …` | every quantifier over a declared letter, in the four theorems that declare one |
| `there is d ∈ ℤ with d > 1, …` where nothing declares d | a range line for three uses | sqrt2-irrational's three |

In a theorem that says what a letter ranges over, every quantifier over the
letter writes the bound, as a textbook does: the set is said once, above,
and "ε ∈ ℝ with ε > 0" says it again. The two are one formula, so this is
only about reading. A range line is worth writing where a letter is
quantified often, as ε and δ are in analysis; sqrt2-irrational quantifies d
three times and writes the set each time rather than add a line to say it.

### "There exists … such that" or "there is … with" is not settled

The two are one formula, written on 14 lines against 30: four theorems state
their conclusion the first way, and each repeats it as its last step, and
the analysis lines use it wherever a trailing universal follows. Which
reads better elsewhere is left open until more of the corpus is written the
new way, since a rule argued from a handful of proofs would be a rule about
those proofs. The same holds for two names, "there exist x, y ∈ ℤ such that"
against "there are x, y ∈ ℤ with": three theorems state their conclusion the
first way, and Bezout's define line is written the second.

One case is settled:

| write | not | today |
|---|---|---|
| `{t ∈ ℕ : there are m, n ∈ ℤ with …}` | `{t ∈ ℕ : there exist m, n ∈ ℤ such that …}` | the one set-builder with an existence inside |

The colon of a set-builder is read "such that", so the textbook words inside
one say "such that" twice in a row: "the t in ℕ such that there exist m and n
such that …". Inside a set-builder, or anywhere a "such that" is already being
read, the existence is written with "with".

## The shape of a step

| write | not | today |
|---|---|---|
| `obtain a, b: item, from L` where the existence comes from an item | an existence step, then `obtain a, b from line L` | all 27 obtains follow it: 24 from an item, 3 from a line |
| an existence step, then `obtain a, b from line L` where the existence comes from a line | `obtain a, b: item, from L` | (the same count) |
| a claim of several sentences | one claim joined by `and` | judgement |
| commas and a final `and` inside a "there is" | repeated `and` | judgement |

The obtain rule is the one with a reason beyond taste. In the one-line form
the name appears in the claim, which is written above the justification that
introduces it, and that is the only place in this language where a name is
used before the line that names it. The claim says everything about the
name it introduces — `r ∈ ℤ. p = 2r.` — so the reader meets r with what it
is, as a textbook's "p = 2r for some integer r" or "choose N with …" does.
Which letter the item happens to use is no part of it: the item is cited and
its text is elsewhere, so `even`'s k never reaches the page, and stating
"there is r ∈ ℤ with p = 2r" first only says the next line twice. An
existence that comes from a line rather than an item has no item to name,
so it takes the second form whatever its letters: the intermediate value
proof obtains δ from a line an `instantiate` gave. An item whose "there is"
is a define's condition, which `part-builder` and `set-builder` hold inside
a conjunction, is an item all the same: Lagrange obtains a coset's a from
K in one line.

The last two are judgement and may stay that way. "A claim that is a
conjunction is written as separate sentences" is in `SYNTAX.md`, but whether a
particular `and` joins two claims or belongs inside one formula is not
something a tool can see from the text.

## What would enforce these

Nothing does. Most are a regular expression over the source line and would be
cheap, the doubled negation among them, `suppose not` before a negated claim; the obtain rule is a justification head and is cheaper
still. The two marked judgement are not mechanical at all and are here so that
a reader of this file knows they were considered rather than missed.

If a linter is written it belongs in the gate beside the checker, and
its findings are suggestions rather than problems. A problem means the corpus
says something it should not, and the gate is red until it is fixed. A
suggestion here means the corpus says the right thing in what we took to be the
harder of two ways, and the proof would be just as true if nobody ever acted on
it. So a suggestion never fails the gate, and a writer who disagrees with one
is disagreeing with a judgement written in this file rather than with a tool.
