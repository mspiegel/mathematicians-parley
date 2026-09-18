# Pilot: there is a prime greater than any natural number

The fourth pilot, written to `SYNTAX.md`. Its purpose is to exercise an
existence proof by construction: the object the theorem asserts is
obtained from a number built for the purpose, n! + 1. It is number 11 on
Wiedijk's list and `infpn` in set.mm, and Hammack proves it in the chapter
on proof by contradiction.

The textbook statement is "there are infinitely many primes". That needs
a definition of "infinitely many", and the standard way round it, which
set.mm also takes, is to state the theorem as: for every natural number
n there is a prime greater than n. That is the form here.

Two things in this file are new. A supposition that is the negation of an
inequality is written literally, `suppose not p > n`, and turned into
p ≤ n by a step, since the contradiction rule requires the supposition to
be the negation of the claim and nothing else. And several cited theorems
are facts a school reader accepts without proof, such as that every
number greater than 1 has a prime factor; they are database items with
pointers, and the pilot does not prove them.

---

## Theorem prime-above

```
theorem prime-above
  let n ∈ ℕ                                                           (H1)
  then there is p ∈ ℕ with p prime and p > n

1.  n! ∈ ℕ
    thm:factorial-nat n := n, from H1

2.  n! + 1 ∈ ℕ
    thm:nat-closure a := n!, b := 1, from 1
    requires 1 ∈ ℕ: arithmetic

3.  n! ≥ 1
    thm:nat-ge-1 m := n!, from 1

4.  n! + 1 > 1
    inequalities, from 3

5.  p ∈ ℕ. p is prime. p divides n! + 1.
    obtain p: thm:prime-factor m := n! + 1, from 2, 4

6.  p > 1
    def:prime p := p, from 5

7.  p > n
    contradiction
    suppose not p > n                                                 (S)

    7.1.  p ≤ n
          inequalities, from S

    7.2.  p divides n!
          thm:factorial-divisible n := n, m := p, from H1, 5, 7.1

    7.3.  p divides (n! + 1) − n!
          thm:divides-difference d := p, a := n! + 1, b := n!, from 5, 7.2
          requires p ∈ ℤ: thm:nat-int, from 5
          requires n! + 1 ∈ ℤ: thm:nat-int, from 2
          requires n! ∈ ℤ: thm:nat-int, from 1

    7.4.  (n! + 1) − n! = 1
          algebra

    7.5.  p divides 1
          substitute (n! + 1) − n! = 1 (7.4) into 7.3

    7.6.  p = 1
          thm:divides-one d := p, from 5, 7.5

    7.7.  not p = 1
          inequalities, from 6

    7.8.  p = 1. not p = 1.
          lines 7.6, 7.7

8.  There is p ∈ ℕ with p prime and p > n.
    exhibit p, from 5, 7
```

---

## Rendered view

**Theorem prime-above.** Let n be a natural number. Then there is a
natural number p with p prime and p > n.

*Proof.*

1. n! ∈ ℕ.
   By the theorem factorial-nat, from the hypothesis n ∈ ℕ. That theorem
   states: let n be a natural number; then n! is a natural number.

2. n! + 1 ∈ ℕ.
   By the theorem nat-closure, with n! as a and 1 as b, from line 1. That
   theorem states: let a and b be natural numbers; then a + b and a·b are
   natural numbers.
   Requires 1 ∈ ℕ, by arithmetic.

3. n! ≥ 1.
   By the theorem nat-ge-1, with n! as m, from line 1. That theorem
   states: let m be a natural number; then m ≥ 1.

4. n! + 1 > 1.
   By the rules for inequalities, from line 3.

5. p ∈ ℕ. p is prime. p divides n! + 1.
   Obtain p by the theorem prime-factor, with n! + 1 as m, from lines 2
   and 4. That theorem states: let m be a natural number; assume m > 1;
   then there is a natural number p with p prime and p divides m.

6. p > 1.
   By the definition of prime, from line 5. That definition states: let p
   be a natural number; p is prime if and only if p > 1 and, for every
   natural number d, if d divides p then d = 1 or d = p.

7. p > n.
   By contradiction. Suppose that not p > n.

   7.1. p ≤ n.
        By the rules for inequalities, from the supposition.

   7.2. p divides n!.
        By the theorem factorial-divisible, with p as m, from the
        hypothesis n ∈ ℕ and lines 5 and 7.1. That theorem states: let n
        and m be natural numbers; assume m ≤ n; then m divides n!.

   7.3. p divides (n! + 1) − n!.
        By the theorem divides-difference, with p as d, n! + 1 as a and
        n! as b, from lines 5 and 7.2. That theorem states: let d, a and b
        be integers; assume d divides a and d divides b; then d divides
        a − b.
        Requires p ∈ ℤ, by the theorem nat-int from line 5. That theorem
        states: let m be a natural number; then m is an integer.
        Requires n! + 1 ∈ ℤ, by the theorem nat-int from line 2.
        Requires n! ∈ ℤ, by the theorem nat-int from line 1.

   7.4. (n! + 1) − n! = 1.
        By algebra.

   7.5. p divides 1.
        By substituting line 7.4 into line 7.3.

   7.6. p = 1.
        By the theorem divides-one, with p as d, from lines 5 and 7.5.
        That theorem states: let d be a natural number; assume d divides
        1; then d = 1.

   7.7. p is not 1.
        By the rules for inequalities, from line 6.

   7.8. p = 1, and p is not 1.
        By lines 7.6 and 7.7.

8. There is a natural number p with p prime and p > n.
   With witness p, from lines 5 and 7.

∎

---

## Database items

Items already listed in earlier pilots are not repeated. The symbol n! is
new.

| symbols | what they are | set.mm |
|---|---|---|
| n! | factorial | cfa |

| pointer | statement | set.mm |
|---|---|---|
| def:factorial | 1! = 1. Let n ∈ ℕ. (n + 1)! = n!·(n + 1). | fac1, facp1 |
| def:prime | Let p ∈ ℕ. p is prime ↔ p > 1 and for every d ∈ ℕ, if d divides p then d = 1 or d = p. | isprm2 |
| thm:factorial-nat | Let n ∈ ℕ. Then n! ∈ ℕ. | facnn |
| thm:nat-closure | Let a ∈ ℕ, b ∈ ℕ. Then a + b ∈ ℕ. a·b ∈ ℕ. | nnaddcl, nnmulcl |
| thm:nat-ge-1 | Let m ∈ ℕ. Then m ≥ 1. | nnge1 |
| thm:nat-int | Let m ∈ ℕ. Then m ∈ ℤ. | nnz |
| thm:prime-factor | Let m ∈ ℕ. Assume m > 1. Then there is p ∈ ℕ with p prime and p divides m. | exprmfct |
| thm:factorial-divisible | Let n ∈ ℕ, m ∈ ℕ. Assume m ≤ n. Then m divides n!. | dvdsfac |
| thm:divides-difference | Let d ∈ ℤ, a ∈ ℤ, b ∈ ℤ. Assume d divides a. Assume d divides b. Then d divides a − b. | dvds2sub |
| thm:divides-one | Let d ∈ ℕ. Assume d divides 1. Then d = 1. | dvds1 |
| thm:prime-above | proved above | infpn |

No new methods. `substitute ... into`, `inequalities`, `lines`,
`obtain`, `exhibit` and `contradiction` are as in `SYNTAX.md`.

---

## What the pilot reveals

1. **The construction is a number, the witness is obtained.** The object
   the proof builds is n! + 1, but the witness for the theorem is p, which
   step 5 obtains from the prime-factor theorem applied to n! + 1. So an
   "existence proof by construction" in this language is an `obtain` from
   a cited existence theorem, followed by steps about the obtained
   object, closed by `exhibit`. Nothing in the syntax marks the
   construction as such; the reader sees it in what n! + 1 is used for.
2. **A supposition is the literal negation.** The claim at step 7 is
   p > n, so the supposition is `not p > n`, and turning that into p ≤ n
   is step 7.1, by the rules for inequalities. Writing `suppose p ≤ n`
   directly would have hidden that step. This is the literal-instance
   rule applied to the contradiction method: the block assumes exactly
   the negation of the claim.
3. **Reaching "P and not P" can take a step.** The block ends with p = 1
   from step 7.6 and p > 1 from step 6, which contradict but are not of
   the form P and not P. Step 7.7 derives "not p = 1" from p > 1 so that
   7.8 can state the pair. This is the same discipline as finding 2, from
   the other side.
4. **The ↔ convention has been in use since the first pilot and is not
   written down.** Step 6 cites def:prime, whose body is "p is prime ↔
   ...", with a line stating "p is prime", and claims one sentence of the
   right-hand side. The √2 pilot did the same with def:even at every
   `obtain` and `exhibit`. `SYNTAX.md` lists the conventions for
   conjunctions, right-to-left equations and conditionals, but not this
   one: given a line stating one side of a cited "A ↔ B", a step may
   claim the other side. It should be added.
5. **Cited principles above the school ceiling.** Three theorems are
   cited without proof here: every number greater than 1 has a prime
   factor, every m ≤ n divides n!, and the only natural number dividing 1
   is 1. A school reader accepts all three and would prove none. They are
   database items with pointers, which is what the pointer rule is for,
   but the corpus is not complete until each has a proof in this
   language, and the first two are themselves proofs by induction or by
   least element. This is the first pilot to lean on the database this
   much, and it shows the corpus will be a tree of theorems, not ten
   isolated files.
6. **Divisibility on ℤ costs three dull facts.** def:divides from the √2
   pilot is stated on ℤ, so divides-difference is too, and citing it for
   natural numbers needs p, n! and n! + 1 moved from ℕ to ℤ, three
   requires lines at 7.3. Stating divides on ℕ for Reader A, with the ℤ
   version as a separate item, would remove them here and add them
   wherever negative numbers appear. The pilot keeps the ℤ definition and
   pays.
7. **"Infinitely many" is avoided, not defined.** The theorem says that
   above every n there is a prime, which is what set.mm's infpn says and
   what Hammack's proof shows. The sentence "there are infinitely many
   primes" would need a definition of infinite for a set, and set.mm's
   infpn2, which says the set of primes is equinumerous with ℕ, is the
   version that carries it. Whether the corpus should state the textbook
   sentence, with the definition it needs, is a question for the
   set-theoretic pilot.

Numbers, for the record: 16 numbered steps, 4 requires lines. set.mm's
infpn has 2 essential steps, resting on infpnlem1 with 58 and infpnlem2
with 38.
