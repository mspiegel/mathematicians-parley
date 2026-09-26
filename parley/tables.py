"""Reading the rule tables: a fact the page leaves out, built by table.

The rule tables are the fourth of the elaborator's six parts (`ELABORATION.md`,
"How the elaborator is built"), and `parley/rules.py` holds them as data.
This is the code that reads them. Given what is wanted — an equation lifted
through a term, a term's membership of a number system, a numeral's, a
term's sethood — it looks up the lemma the table names for that shape and
builds the proof from it. Nothing here searches: what a table has no entry
for is declined, and left to what is tried after.
"""
import contextlib
from fractions import Fraction

import field
import linear
import normal
import rules
from parse import Declined, declined
from provenance import from_requires


class TableReading:
    @contextlib.contextmanager
    def writing(self, scope, known, keep=False):
        """What the step's requires lines made, offered while a step is built.

        `written` is what the membership lookup (`part`, `membership`) and
        the one-lemma bridge read before any search, and a search never
        does, so offering these widens nothing `settle` looks through. Only
        what a requires line made is offered, including where the scope
        holds the same claim for another reason: that is the case a line
        like `requires x ∈ ℝ: from H1` is written for. `keep` lays these
        over what is already offered rather than in its place.
        """
        kept = self.written
        made = {k: (scope, v) for k, v in known.items() if from_requires(v)}
        self.written = {**kept, **made} if keep else made
        try:
            yield
        finally:
            self.written = kept

    def within(self, said, system, scope, facts, depth):
        """`said ∈ system` searched for, at the depth the caller gives.

        For a caller whose term is deeper than a side condition, as a
        method's own claim may be: `part` first, from the step's own lines,
        is the caller's to try.
        """
        return self.settle(self.to_term(self.seq(said, system, 'wcel')),
                           scope, facts, depth=depth)

    def congruence(self, given, want, scope, facts, step, leaf):
        """Carry one change up to the whole term it sits in.

        Two terms that differ in one place are walked in step, and the
        lemma that lifts each level is the one the tree names: the walk
        `descend` makes over a readable claim, made here over a term the
        kernel holds. What counts as the change, and what proves it there,
        is the caller's.

        What it refuses is a route declining and not a defect, however it
        was reached. It used to carry the step's line where a caller had a
        step and none where one did not, so the same failure was a defect
        or a decline according to who was on the stack.
        """
        found = leaf(given, want, scope, facts)
        if found is not None:
            return found
        if (given.label != want.label
                or len(given.children) != len(want.children)):
            return self.no(
                '{} and {} differ by more than the change being carried',
                given.rpn(self.flabel), want.rpn(self.flabel))
        if given.label == 'wrex':
            body, variable, over = given.children
            name, runs = variable.rpn(self.flabel), over.rpn(self.flabel)
            # Only the body is carried under the binder; a change in what it
            # binds or where that runs is not this walk's to make.
            if [c.rpn(self.flabel) for c in want.children[1:]] \
                    != [name, runs]:
                return Declined('the two bind differently')
            # `rexbidva` keeps its letter apart from the scope it carries,
            # as `sumeq2sdv` does its index (`summand_changed`).
            if name in scope.split():
                return Declined('the scope mentions the letter this binds')
            member = self.seq(f'{name} cv', runs, 'wcel')
            # The scope under a binder belongs to the walk and to nothing
            # else (`frames_kept`).
            with self.frames_kept():
                inner, lifted = self.widen(scope, facts, member)
                made = self.congruence(body, want.children[0], inner, lifted,
                                       step, leaf)
            if declined(made):
                return made
            return self.seq(scope, body.rpn(self.flabel),
                       want.children[0].rpn(self.flabel), name, runs, made,
                       'rexbidva')
        # A sum's summand is carried the same way, under its index's range:
        # T(k) is its rule only for k in T's domain, and the sum is what
        # says where k runs.
        if given.label == 'csu' \
                and given.children[0].rpn(self.flabel) \
                == want.children[0].rpn(self.flabel) \
                and given.children[2].rpn(self.flabel) \
                == want.children[2].rpn(self.flabel) \
                and given.children[1].rpn(self.flabel) \
                != want.children[1].rpn(self.flabel):
            runs, body, index = given.children
            name = index.rpn(self.flabel)
            if name in scope.split():
                return Declined('the scope mentions the letter this binds')
            member = self.seq(f'{name} cv', runs.rpn(self.flabel), 'wcel')
            with self.frames_kept():
                inner, lifted = self.widen(scope, facts, member)
                made = self.congruence(body, want.children[1], inner, lifted,
                                       step, leaf)
            if declined(made):
                return made
            return self.ap('sumeq2dv', {'ph': scope,
                                        'A': runs.rpn(self.flabel),
                                        'B': body.rpn(self.flabel),
                                        'C': want.children[1].rpn(self.flabel),
                                        'k': name}, made)
        wrapped = given.label in rules.WRAPS
        kids = given.children[:-1] if wrapped else given.children
        wants = want.children[:-1] if wrapped else want.children
        spelt = [c.rpn(self.flabel) for c in kids]
        other = [c.rpn(self.flabel) for c in wants]
        slots = [i for i in range(len(kids)) if spelt[i] != other[i]]
        if not slots:
            return Declined('nothing changed under this term')
        # What lifts the change is the lemma for this constructor and these
        # places, and the operation it lifts under must be the same one.
        lifting = rules.CONGRUENCE.get((given.label, tuple(slots)))
        if lifting is None or (wrapped and given.children[-1].rpn(self.flabel)
                               != want.children[-1].rpn(self.flabel)):
            return Declined('no lemma carries this change up')
        # The lemmas that carry a change under a binder keep its letter
        # apart from the scope, as `rexbidva` does above.
        if given.label in rules.BOUND and len(given.children) >= 2 \
                and given.children[1].rpn(self.flabel) in scope.split():
            return Declined('the scope mentions the letter this binds')
        moved = [x for i in slots for x in (spelt[i], other[i])]
        rest = [s for i, s in enumerate(spelt) if i not in slots]
        head = given.children[-1].rpn(self.flabel) if wrapped else ''
        under = [self.congruence(kids[i], wants[i], scope, facts, step, leaf)
                 for i in slots]
        for one in under:
            if declined(one):
                return one
        return self.seq(scope, *moved, *rest, head, *under, lifting)

    def numeral_within(self, goal, scope, facts):
        """( scope -> t e. S ), for a term built from numerals alone.

        A digit set.mm names in the system is its label. Anything else built
        only from numerals — 10, which is the decimal `; 1 0`, or 9, which
        set.mm puts in ℕ and not in ℤ by name, or 10^0 − 1 — is settled from
        the declared closure lemmas, which is working it out and not
        searching: there is no letter in it for a fact to be about.
        """
        named = self.digit_within(goal, scope, facts)
        if not declined(named):
            return named
        said = goal.children[0].rpn(self.flabel)
        if set(said.split()) - rules.NUMERIC:
            return named
        # One level deeper than `settle`'s default, which is chosen for
        # chains through a proof's own facts: 10^0 − 1 ∈ ℤ is `zsubcl`, then
        # `nn0z`, `nn0expcl` and `deccl`. `settle` sends a number here
        # first, so while this term is being worked out it is searched
        # for there like any other.
        # Nothing in it is a proof's own, so what it comes to is the same
        # wherever it is asked under this scope, and is worked out once.
        # Only where it rests on nothing on the page, though: the search
        # also reads a step's own requires lines, and a proof of 10 ∈ ℝ
        # made from one step's `10 ∈ ℤ` line, handed to the next step,
        # rested on a line that step did not name.
        want = goal.rpn(self.flabel)
        if (want, scope) in self.numbers:
            return self.numbers[want, scope]
        self.numbering.add(want)
        try:
            found = self.settle(goal, scope, {}, depth=4)
            if declined(found):
                found = self.by_value(goal, scope)
        finally:
            self.numbering.discard(want)
        if declined(found) or not getattr(found, 'origin', None):
            self.numbers[want, scope] = found
        return found

    def by_value(self, goal, scope):
        """( scope -> t e. S ) for a closed t, through the digit it comes to.

        The closure lemmas build a membership from the parts' and cannot
        build every one: a difference of whole numbers need not be whole, so
        nothing puts 0 − 0 in ℕ₀, which the binomial theorem's term at n = 0
        asks of its exponent. It is 0, which is. So the equation is worked
        out as `arithmetic` works one out, and the membership is the
        digit's, carried across it by `eqeltrd`.
        """
        said, system = goal.children
        value = field.closed_value(said, self.flabel)
        if declined(value):
            return value
        if not isinstance(value, Fraction) or value.denominator != 1 \
                or not 0 <= value <= 9:
            return Declined('it does not come to a digit')
        digit = field.NUMERAL[int(value)]
        if said.rpn(self.flabel) == digit:
            return Declined('it is a digit already')
        member = self.digit_within(
            self.to_term(self.seq(digit, system.rpn(self.flabel), 'wcel')),
            scope, {})
        if declined(member):
            return member
        same = self.prove_field(
            None, self.seq(said.rpn(self.flabel), digit, 'wceq'), scope, {},
            None)
        if declined(same):
            return same
        return self.ap('eqeltrd', {'ph': scope, 'A': said.rpn(self.flabel),
                                   'B': digit,
                                   'C': system.rpn(self.flabel)},
                       same, member)

    def decimal_within(self, goal, scope):
        """( scope -> ; A B e. S ), for a numeral of more than one digit.

        `deccl` puts a decimal in ℕ₀ from its parts being there, and asks
        that as closed facts rather than under a scope, so it is built here
        from the digits' labels and brought into the scope once, and never
        offered to `settle`, whose proofs stand under one.
        """
        said, system = goal.children
        if system.label not in rules.FROM_NN0:
            return Declined('a decimal is placed in ℕ₀, ℤ, ℝ and ℂ only')

        def whole(term):
            if term.label in field.DIGITS and not term.children:
                return self.seq(f'{field.DIGITS[term.label]}nn0')
            if term.label != 'cdc':
                return Declined('not a numeral')
            upper, last = term.children
            parts = [whole(upper), whole(last)]
            if any(declined(p) for p in parts):
                return next(p for p in parts if declined(p))
            return self.ap('deccl', {'A': upper.rpn(self.flabel),
                                     'B': last.rpn(self.flabel)}, *parts)

        closed = whole(said)
        if declined(closed):
            return closed
        lift = rules.FROM_NN0[system.label]
        if lift is not None:
            closed = self.ap(lift, {'A': said.rpn(self.flabel),
                                    'N': said.rpn(self.flabel)}, closed)
        return self.seq(goal.rpn(self.flabel), scope, closed, 'a1i')

    def digit_within(self, goal, scope, facts):
        """( scope -> d e. S ), for a digit and a system set.mm names it in.

        `ax-1cn` is the one place the library spells such a label otherwise,
        and where it names none the fact is one it does not state: `0 e. NN`
        is false and `2 e. QQ` unwritten. Both decline here, which leaves
        them where a claim this method cannot decide belongs.
        """
        said, system = goal.children
        suffix = rules.SYSTEMS.get(system.label)
        if suffix is None or system.children:
            return Declined('not a number system set.mm names digits in')
        if said.label == 'cdc':
            return self.decimal_within(goal, scope)
        value = linear.numeral(said, self.flabel)
        if value is None or value.denominator != 1 \
                or not 0 <= int(value) <= 9:
            return Declined('what belongs is not a single digit')
        digit = int(value)
        # As in the relation above: the side must *be* its digit. One that
        # only works out to it is a computation, and this is not the method
        # that does computations.
        if said.rpn(self.flabel) != field.NUMERAL[digit]:
            return Declined('a side works out to a digit but is one '
                            'only after working out')
        label = f'{digit}{suffix}'
        if label not in self.sigs:
            label = f'ax-{label}'
        if label not in self.sigs and suffix == 'z' \
                and f'{digit}nn0' in self.sigs:
            # set.mm names every digit in ℕ₀ and only some in ℤ: `9nn0` is
            # there and `9z` is not.
            closed = self.ap('nn0zi', {'N': field.NUMERAL[digit]},
                             self.seq(f'{digit}nn0'))
            return self.seq(self.seq(field.NUMERAL[digit], system.label,
                                     'wcel'), scope, closed, 'a1i')
        if label not in self.sigs:
            return Declined(f'set.mm does not state '
                            f'{self.render(goal.rpn(self.flabel))}')
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope,
                                                        facts))
        return work.a1i(self.seq(field.NUMERAL[digit], system.label, 'wcel'),
                        label)

    def membership(self, said, system, scope, facts):
        """That a term belongs to a number system, which the text writes.

        `READERS.md` settles that membership is a dull fact the page states
        rather than a step's to discover, and records the price: ninety-seven
        such lines across the forty-two steps citing `algebra` or
        `inequalities`, the exemption having been rejected. So a term whose
        membership nothing supplies is a line the proof owes, and saying so
        is what this is for.

        The methods reach here for every atom they do not look inside, and
        they reach it while writing rather than while deciding. A decline
        given back from here would reach the caller as the method not
        covering the step, which is the one thing it does not mean.
        """
        want = self.seq(said, system, 'wcel')
        # What the step's own lines say, first. The scope may hold the same
        # claim with another origin — `abs-bounds` writes `requires x ∈ ℝ:
        # from H1` beside the hypothesis saying `x ∈ ℝ` — or a claim one
        # lemma away — `k ∈ ℤ` from the line that obtained k, where the step
        # wrote `k ∈ ℝ` and wants `k ∈ ℂ` — or the claim whole where the step
        # names only its parts, as the triangle inequality's step 5.2 names
        # `a ∈ ℝ` and `b ∈ ℝ` and line 1 says `a + b ∈ ℝ`. In each the line
        # the step names is the one to use; `part` says in what order.
        found = self.part(said, system, scope, facts)
        if not declined(found):
            return found
        # What `part` cannot build is searched for, with the step's own lines
        # laid over the scope's copies of the same claims. They replace those
        # copies and add almost nothing, so the search is no wider than it
        # was, and what it finds rests on the lines the step names.
        written = {k: v for k, v in facts.items() if from_requires(v)}
        for k, (at, v) in self.written.items():
            lifted = self.lifted_to(k, v, at, scope)
            if lifted is not None:
                written[k] = lifted
        found = self.settle(self.to_term(want), scope, {**facts, **written})
        if declined(found):
            raise self.defect(
                self.at, f'nothing says {self.render(want)}, which this step '
                         f'needs')
        return found

    def bridged(self, said, system, scope, written):
        """`said ∈ system`, carried in one lemma from a membership written.

        Only the lemmas `rules.MEMBERSHIP` declares that take a thing in
        one number system to another — `recn`, `zcn`, `nnre` — and only one
        of them. Settling from the written facts instead searches everything
        that could reach the claim, and where nothing written does, that
        search is what costs: `abs-bounds` spent four and a half million
        `fits` calls in it on one membership.
        """
        if self.bridges is None:
            self.bridges = {}
            for label in self.declared_as('carrier'):
                given, gives = self.syntax.statement(self.sigs[label]).children
                self.bridges.setdefault(
                    (given.children[1].rpn(self.flabel),
                     gives.children[1].rpn(self.flabel)), label)
        for (source, target), label in self.bridges.items():
            if target != system:
                continue
            claim = self.seq(said, source, 'wcel')
            proof = written.get(claim)
            if proof is None:
                held = self.written.get(claim)
                if held is not None:
                    proof = self.lifted_to(claim, held[1], held[0], scope)
            # What a requires line wrote, or what a line being cited says:
            # `requires |f(x₁) − f(c)| ∈ ℝ: thm:stdlib/numbers/abs-real …,
            # from 17.14` wants the difference in ℂ and cites the line saying
            # it is real, and without this the lemmas were searched in their
            # order, 25 seconds of it, to reach the same fact.
            origin = getattr(proof, 'origin', frozenset())
            if proof is None or not (from_requires(proof)
                                     or (origin and origin <= self.citing)):
                continue
            return self.ap('syl', {'ph': scope, 'ps': claim,
                                   'ch': self.seq(said, system, 'wcel')},
                           proof,
                           self.ap(label, {self.sigs[label].push[0]: said}))
        return None

    def sethoods(self, nodes, terms, scope, facts):
        """The sethood of each class a statement's `let` lines introduce.

        In the kernel's sense — not a proper class — which the page never
        says (`READERS.md`, hidden entirely): `let a ∈ X` makes a a set by
        `elex`, and `let a ∉ X` and `let x be an element` by the conjunct
        `hypothesis_body` adds. Each goes into `facts` sealed as
        `sethood@<label>`, and those origins are what this gives back, for
        `self.sorts`: a step rests on a thing's sethood as it rests on
        `let X be a set`, without naming the line. `be a set` is already a
        sort.
        """
        out = set()
        for h, node, t in zip(self.thm.hypotheses, nodes, terms, strict=True):
            if h[0] != 'let' or not h[2] or ' be a set' in h[1]:
                continue
            kernel = self.names.get(self.subject_of(node).text)
            if kernel is None:
                continue
            said = self.seq(kernel, 'cvv', 'wcel')
            origin = f'sethood@{h[2]}'
            if said in facts:
                facts[said] = self.seal(facts[said], origin)
            elif node.notation == 'membership' and t in facts:
                a, b = (c.rpn(self.flabel) for c in self.to_term(t).children)
                facts[said] = self.seal(
                    self.seq(scope, t, said, facts[t],
                             self.ap('elex', {'A': a, 'B': b}), 'syl'),
                    origin)
            else:
                continue
            out.add(origin)
        return out

    def made_a_set(self, wanted, scope, facts):
        """`term ∈ V` from the constructor at the term's head; else a decline.

        `SETHOOD` names the lemma, and `apply_lemma` asks what it asks — the
        parts' sethood — of `settle`, which comes back here for each part. A
        part that is a class the statement introduced is a fact already,
        sealed as a sort in `run`. Nothing is searched: a term whose head is
        not in the table declines, and the table's lemmas in
        `rules.MEMBERSHIP` are what is tried after.
        """
        head = wanted.children[0]
        lemma = rules.SETHOOD.get(head.label) if head.variable is None else None
        if lemma is None:
            return Declined(f'no lemma makes a {head.label} a set')
        return self.apply_lemma(lemma, wanted, scope, facts, None,
                                crossing=False)

    def built(self, said, system, scope, parts, nonzero=None):
        """`said ∈ system` for a compound, from its parts; else a decline.

        A sum of reals is real by `readdcld` from its two parts being real.
        What each part is proved by is the caller's: `parts(term, system)`.
        A method takes a part from what the step's own line says of it
        (`part`). Searched for instead, `settle` tries its lemmas in their
        order and `zcn` comes before `mulcl`, so `a·x₀ ∈ ℂ` was reached
        through `a ∈ ℤ` from the hypothesis rather than through `a ∈ ℝ` from
        the line the page wrote. A side condition takes a part from `settle`
        (`closed_under`). A fixed table and no search, so nothing it cannot
        build costs more than a lookup.

        A quotient is built only where `nonzero(divisor)` is given to prove
        its divisor is not zero: telescoping 2/k over k from 1 asks that
        2/k be a number, and k ≠ 0 is what the range gives.
        """
        node = self.to_term(said)
        if node.variable is None and node.label == 'co' \
                and len(node.children) == 3:
            left, right, op = node.children
            op = op.rpn(self.flabel)
            if op == 'cdiv' and nonzero is not None \
                    and system in rules.DIVIDED:
                a, b = left.rpn(self.flabel), right.rpn(self.flabel)
                pa = parts(a, system)
                if declined(pa):
                    return pa
                pb = parts(b, system)
                if declined(pb):
                    return pb
                pn = nonzero(b)
                if declined(pn):
                    return pn
                return self.ap(rules.DIVIDED[system],
                               {'ph': scope, 'A': a, 'B': b}, pa, pb, pn)
            lemma = rules.CLOSED.get((op, system))
            if lemma is None:
                return Declined(f'no closure lemma for {op} in {system}')
            a, b = left.rpn(self.flabel), right.rpn(self.flabel)
            pa = parts(a, system)
            if declined(pa):
                return pa
            pb = parts(b, 'cn0' if op == 'cexp' else system)
            if declined(pb):
                return pb
            return self.ap(lemma, {'ph': scope, 'A': a,
                                   'N' if op == 'cexp' else 'B': b}, pa, pb)
        if node.variable is None and node.label == 'cneg' \
                and len(node.children) == 1:
            lemma = rules.NEGATED.get(system)
            if lemma is None:
                return Declined(f'no closure lemma for negation in {system}')
            a = node.children[0].rpn(self.flabel)
            pa = parts(a, system)
            if declined(pa):
                return pa
            return self.ap(lemma, {'ph': scope, 'A': a}, pa)
        return Declined('not a sum, difference, product, power or negation')

    def closed_under(self, wanted, scope, facts, depth):
        """A compound's membership of a number system, from its parts'.

        A product of three factors is real because each factor is, and
        searched for, each product is a lemma spent: the binomial theorem's
        summand C(m, k)·x^(m − k)·y^k is two products, a power, and a
        coefficient that is complex through ℕ₀, past any depth a search is
        given. Walking the term by `CLOSED` spends none, as splitting a
        conjunction spends none: there is one way to build a product from
        its factors, and the factors are smaller. Each factor is settled in
        turn with the depth the whole was given.
        """
        return self.built(
            wanted.children[0].rpn(self.flabel),
            wanted.children[1].rpn(self.flabel), scope,
            lambda term, system: self.settle(
                self.to_term(self.seq(term, system, 'wcel')), scope, facts,
                depth),
            lambda divisor: self.settle(
                self.to_term(self.seq(divisor, 'cc0', 'wne')), scope, facts,
                depth))

    def divisor_written(self, divisor, scope, facts):
        """( scope -> d =/= 0 ) from what the step wrote, or a decline.

        A quotient's membership is built from its parts' as a sum's is
        (`METHODS.md`, the hypothesis a reciprocal atom brings), and the
        divisor not being zero is the one thing more it asks. It is the
        page's to say, in a requires line or a line the step cites, and is
        not searched for.
        """
        apart = self.seq(divisor, 'cc0', 'wne')
        # A digit other than zero says so itself: a closed numeral fact,
        # which a method may use unwritten (`METHODS.md`). δ/2 is real
        # because δ is.
        value = field.DIGITS.get(divisor)
        if value:
            return self.seq(apart, scope,
                            'ax-1ne0' if value == 1 else f'{value}ne0', 'a1i')
        denied = self.seq(self.seq(divisor, 'cc0', 'wceq'), 'wn')
        for want in (apart, denied):
            found = facts.get(want)
            if found is None:
                held = self.written.get(want)
                if held is not None:
                    found = self.lifted_to(want, held[1], held[0], scope)
            if found is None:
                continue
            if want == apart:
                return found
            return self.seq(scope, divisor, 'cc0', found, 'neqned')
        return Declined(f'nothing the step wrote says {self.render(apart)}')

    def part(self, said, system, scope, facts):
        """One part of a compound, in a number system, or a decline.

        The step's own line first, then that line carried by one lemma, then
        the part built in turn if it is a compound. A numeral is the
        library's. What the scope holds is last, and only exactly: it is a
        line the page wrote, and a step using it without naming it is what
        provenance is there to see.
        """
        want = self.seq(said, system, 'wcel')
        found = facts.get(want)
        if found is not None and from_requires(found):
            return found
        held = self.written.get(want)
        if held is not None:
            lifted = self.lifted_to(want, held[1], held[0], scope)
            if lifted is not None:
                return lifted
        carried = self.bridged(said, system, scope, facts)
        if carried is not None:
            return carried
        term = self.to_term(said)
        if linear.numeral(term, self.flabel) is not None:
            return self.settle(self.to_term(want), scope, facts)
        made = self.built(said, system, scope,
                          lambda term, into: self.part(term, into, scope,
                                                       facts),
                          lambda divisor: self.divisor_written(divisor, scope,
                                                               facts))
        if not declined(made):
            return made
        if found is not None:
            return found
        return Declined(f'nothing written says {self.render(want)}')
