# Lint rules

A lint rule is one that can be broken by text that parses, passes the checker,
and is correct. Nothing here is about a proof being wrong. Every rule below
says that one of two correct ways of writing the same thing is harder to
understand than the other, and asks for the easier one.

That is the division of labour. The checker decides whether a proof is right,
and has nothing to say about how it reads. A linter decides how it reads, and
has nothing to say about whether it is right. Neither can do the other's job,
and a finding from one should never be reported as though it came from the
other.

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
| `x ∉ B` | `not x ∈ B` | 14 with the sign, none with the word |
| `n is not odd` | `not (n is odd)` | 4 with the word, none with `not` |
| `there is no d ∈ ℤ with …` | `not there is d ∈ ℤ with …` | 3 with the word, none with `not` |

The sign wins for membership because it is the notation a school reader meets
first and the alternative is three words. The word wins for the other two
because the alternatives need brackets, or read as "not there is", which is not
English. Both rules were settled by picking the form the corpus mostly already
used and making the rest agree.

### The negated equality is not settled

`x ≠ y` and `not x = y` are both written, 12 places against 10, and which one a
reader gets more easily depends on where it stands. A plain negated equality is
easier as `x ≠ y`. Two places write a doubled negation, `not not f(x) = B`,
where the sign would give `not f(x) ≠ B`, a double negative that takes longer
to read rather than less. Two more write the closing pair of a contradiction
block, `p = 1. not p = 1.`, where the word form mirrors the claim above it and
the sign breaks the mirror.

So the rule is either "the sign, except where the negation is doubled or
mirrors a claim", which is three clauses and hard to apply, or nothing. It is
left open, because a rule that has to be argued about at each use makes the
text harder to read rather than easier, which is the opposite of the point.

## The shape of a step

| write | not | today |
|---|---|---|
| an existence step, then `obtain a, b from line L` | `obtain a, b: item, from L` | 5 in the long form, 8 compressed |
| a claim of several sentences | one claim joined by `and` | judgement |
| commas and a final `and` inside a "there is" | repeated `and` | judgement |

The obtain rule is the one with a reason beyond taste. In the compressed form
the name appears in the claim, which is written above the justification that
introduces it, and that is the only place in this language where a name is used
before the line that names it. Everywhere else `let` and `define` come first.
The Bezout proof was rewritten to the long form; eight steps in four other
proofs still use the compressed one.

The last two are judgement and may stay that way. "A claim that is a
conjunction is written as separate sentences" is in `SYNTAX.md`, but whether a
particular `and` joins two claims or belongs inside one formula is not
something a tool can see from the text.

## What would enforce these

Nothing does. Four of the seven are a regular expression over the source line
and would be cheap; the obtain rule is a justification head and is cheaper
still. The two marked judgement are not mechanical at all and are here so that
a reader of this file knows they were considered rather than missed.

If a linter is written it belongs in the gate beside ruff and the checker, and
its findings are warnings rather than problems. A problem means the corpus says
something it should not. A warning here means the corpus says the right thing
in the harder of two ways, and the proof would be just as true if nobody ever
acted on it.
