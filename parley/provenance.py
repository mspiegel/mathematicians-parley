"""The proof rules: what a step's proof may rest on, and what it must use.

This is the sixth of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given a finished step's proof and what the step names,
it refuses a proof that rests on anything the step does not name (R1), a
`requires` line or a named line that does no work, and a `requires` line
whose proof does not come from its reason (R2). The section on provenance
states the rules.

A proof carries its `origin`, the page items it rests on. `seal` makes a
proof stand for one item from then on, and keeps what it was built from in
`rests_on`, so a line is asked the same of its own reason and a use is
traced through the lines that use it.
"""
import contextlib

import linear
import rules
import targets
from parse import Declined, citations, declined, fmt, resolve
from spell import Proof

REQUIRES = 'requires@'


def requirement(line):
    """What a `requires` line is called as the origin of a proof.

    It has no number of its own, so it is named by where it stands.
    """
    return f'{REQUIRES}{line}'


def from_requires(proof):
    """Whether a `requires` line made this proof."""
    return any(o.startswith(REQUIRES) for o in getattr(proof, 'origin', ()))


class ProofRules:
    def atoms_of(self, rpn, atoms, terms):
        """The atoms of a claim a method combined, and every term in it.

        An atom is what the method treats as a number it knows nothing
        about: a name, an absolute value, a function's value, a power whose
        exponent is not a numeral. Sums, differences, products, quotients,
        negations and numeral powers are looked inside; numerals are not
        atoms. `METHODS.md`: each atom is a real number, which the step
        writes or cites.

        A numeral of more than one digit is an atom to the method, which
        reads only digits, but not to the page: 10 is a number to a reader
        as 3 is, and `deccl` is what says so, so the step is not asked to.
        """
        def walk(node):
            if node.variable is None and node.label in rules.RELATIONS:
                kids = node.children[:2] if node.label == 'wbr' \
                    else node.children
                for kid in kids:
                    walk(kid)
                return
            terms.add(node.rpn(self.flabel))
            if linear.numeral(node, self.flabel) is not None \
                    or node.label == 'cdc':
                return
            if node.variable is None and node.label == 'co' \
                    and len(node.children) == 3:
                op = node.children[2].rpn(self.flabel)
                if op in rules.ARITHMETIC:
                    walk(node.children[0])
                    walk(node.children[1])
                    return
                if op == 'cexp' and linear.numeral(
                        node.children[1], self.flabel) is not None:
                    walk(node.children[0])
                    return
            if node.variable is None and node.label == 'cneg':
                walk(node.children[0])
                return
            atoms.add(node.rpn(self.flabel))
        walk(self.to_term(rpn))

    def does_work(self, step, number, proof):
        """Everything a step names does work, or a defect names what does not.

        A cited line or requires line is at work where the proof rests on it,
        directly or through another of the step's requires lines. On a
        method step a requires line is also at work where the method demands
        it without the kernel needing it — a membership of an atom of what
        was combined, a term of it not zero — and each such atom's membership
        must be on the page. A step citing an item is the checker's to judge,
        since the item's statement says what it asks.
        """
        head = step.just.head if step.just else ''
        if head.startswith(('def:', 'thm:')):
            return
        used = set(getattr(proof, 'origin', ()))
        todo = [u for u in used if u.startswith(REQUIRES)]
        while todo:
            for more in self.rests_on.get(todo.pop(), ()):
                if more not in used:
                    used.add(more)
                    if more.startswith(REQUIRES):
                        todo.append(more)
        for ref in dict.fromkeys(step.just.refs):
            if ref not in used and ref not in self.sorts:
                raise self.defect(step.line, f'step {number} cites {ref} and '
                                             f'uses nothing it says')
        atoms, terms = set(), set()
        for claim in self.combined.get(step.line, ()):
            self.atoms_of(claim, atoms, terms)
        written = {}
        for text, _how, line in step.requires:
            claim = self.to_term(self.term(self.read(text)))
            written[line] = claim
            if requirement(line) in used:
                continue
            if claim.label == 'wcel':
                demanded = claim.children[0].rpn(self.flabel) in atoms
            elif claim.label == 'wne':
                demanded = claim.children[0].rpn(self.flabel) in terms
            elif claim.label == 'wn' and claim.children[0].label == 'wceq':
                demanded = claim.children[0].children[0].rpn(
                    self.flabel) in terms
            else:
                demanded = False
            if not demanded:
                raise self.defect(line, f'the requires line of step {number} '
                                        f'says {text.strip()}, and the step '
                                        f'neither uses nor asks for it')
        cited = {part for ref in step.just.refs if ref in self.lines
                 for part in self.parts(self.lines[ref].term)}
        for atom in sorted(atoms):
            said = any(c.label == 'wcel' and c.children[0].rpn(self.flabel)
                       == atom for c in written.values())
            said = said or any(
                self.to_term(p).label == 'wcel'
                and self.to_term(p).children[0].rpn(self.flabel) == atom
                for p in cited)
            if not said:
                # By the name the page writes, where the atom is one.
                shown = next((name for name, kernel in self.names.items()
                              if kernel == atom), self.render(atom))
                raise self.defect(step.line,
                                  f'step {number} combines {shown}, and '
                                  f'nothing it writes or cites says it is a '
                                  f'number')

    def combining(self, *terms):
        """Record what a method step's claim is built from.

        The claim and the sentences of cited lines the method combined —
        which the certificate says, not every sentence a cited line says.
        `METHODS.md`: an atom is one of these, and each is real.
        """
        self.combined.setdefault(self.at, set()).update(terms)

    def named(self, step, number, block=False):
        """What a step names, which is everything its proof may rest on.

        The lines it cites and its own requires lines, and the sorts in
        scope. A block also rests on its own steps and on what it assumes,
        and on the lines a `join` inside it names: a join that closes a
        contradiction emits nothing, and the block's close uses what it
        joined (`ELABORATION.md` requirement 8).
        """
        out = set(step.just.refs) | self.sorts
        out |= {requirement(line) for _t, _h, line in step.requires}
        if block:
            out |= {k for k in self.lines if k.startswith(number + '.')}
            out |= {o[2] for o in step.openers if o[2]}
            out.add(f'{number} assumes')
            depth = number.count('.') + 1
            for inner in self.thm.steps:
                name = '.'.join(str(p) for p in inner.number)
                if name.startswith(number + '.') \
                        and name.count('.') == depth \
                        and inner.just.head == 'join':
                    out |= set(inner.just.refs)
        return out

    def discharged_by(self, made, step, how, line):
        """A requires line's proof, checked against its reason and sealed.

        It rests only on the lines its reason cites, the step's other
        requires lines, which `check.py` also lets one line discharge from
        another, and the sorts in scope.
        """
        self.rests_on_named(made, self.reason_allows(step, how), line,
                            'the requires line')
        return self.seal(made, requirement(line))

    def reason_allows(self, step, how):
        """What a requires line with this reason may rest on (R2)."""
        return frozenset(set(citations(how)) | self.sorts
                         | {requirement(one) for _t, _h, one in step.requires})

    def rests_on_named(self, proof, allowed, line, what):
        """A proof resting on nothing its line does not name, or a defect.

        `GOALS.md` decision 9: the kernel proof is derived from the text, so
        what it rests on is what the text says it rests on. A proof that
        verifies while resting on something else says nothing is wrong, and
        this is where that is said.
        """
        extra = sorted(getattr(proof, 'origin', frozenset()) - allowed)
        if extra:
            shown = ', '.join(f'the requires line at {e[len(REQUIRES):]}'
                              if e.startswith(REQUIRES) else e for e in extra)
            raise self.defect(line, f'{what} rests on {shown}, which it does '
                                    f'not name')

    def seal(self, proof, item):
        """The proof, standing from here on for one thing on the page.

        What a later step builds from it rests on `item` and not on whatever
        `item` was itself built from, which is the question each step is
        asked about: what it names against what it used. What the proof was
        built from is kept in `rests_on`, which is how a line is asked the
        same of its own reason, and how a line's uses are traced through the
        lines that use it.
        """
        self.rests_on[item] = (self.rests_on.get(item, frozenset())
                               | getattr(proof, 'origin', frozenset()))
        return Proof(proof.items, {item})

    def check_step(self, proof, step, number, block=False):
        """A step's finished proof, checked by the rules and sealed.

        It rests on nothing the step does not name (R1), everything the
        step names does work, and from here on the proof stands for the
        step's number. What the step names is `named`, which is also what
        `resting_on` offers the search while the step is built, so what the
        search may use and what the check allows are one set. A block names
        its own steps and assumption as well.
        """
        self.rests_on_named(proof, self.named(step, number, block=block),
                            step.line, f'step {number}')
        self.does_work(step, number, proof)
        return self.seal(proof, number)

    @contextlib.contextmanager
    def resting_on(self, allowed):
        """What the proof being built may rest on, while it is built.

        `settle` is offered only facts resting on these. The scope holds
        more, and a side condition answered from a line the step does not
        name is one R1 refuses afterwards; offered it, the search takes
        whichever route the lemma table reaches first. Step 1.2.1.8 of the
        subsets proof cites that T has 2^k elements, and a shallower search
        found T finite through the bijection of 1.2.1.4 instead.
        """
        kept, self.resting = self.resting, allowed
        try:
            yield
        finally:
            self.resting = kept

    def scope_origin(self, scope, facts):
        """The page items a scope is the conjunction of."""
        out, todo = set(), [scope]
        while todo:
            one = todo.pop()
            held = getattr(facts.get(one), 'origin', None)
            if held:
                out |= held
                continue
            node = self.to_term(one)
            if node.variable is None and node.label == 'wa' \
                    and len(node.children) == 2:
                todo.extend(c.rpn(self.flabel) for c in node.children)
        return frozenset(out)

    def supplied(self, step, scope, facts):
        """The facts a step's own `requires` lines put within reach.

        A lemma asks for what it asks for, and the text writes what a reader
        would want written: `resqrtth` wants 0 ≤ 2 and the step says so. The
        lines are proved once and offered alongside what the scope holds.

        A lemma applied where no step is passed has none of these to read,
        and what the scope holds is all there is.

        A line naming an item is that item cited, and citing it asks the
        step for its own `requires` lines again. The one being proved is
        not among what can prove it, so it is held out while it is.
        """
        known = dict(facts)
        for text, how, line in (step.requires if step is not None else ()):
            want = self.read(text)
            term = self.term(want)
            if term in self.supplying:
                continue
            # A claim the scope already holds is taken as it stands only
            # where this line's own reason made that proof. This runs more
            # than once for a step, and what one pass proves is passed on to
            # the next, so that is the common case. Held for any other
            # reason, the proof rests on something the line does not say:
            # `isosceles` holds `A ≠ B` from its hypothesis, and the line
            # asking for it says it comes from line 6. A line resting on the
            # lines it cites is read from them, which is a lookup — except
            # where an earlier pass already did: this line's own proof
            # carries the line as its origin, and was checked against its
            # reason when it was made. Read again, a fact the scope took from
            # a line's naming (`c ∈ ℝ` from an obtain) is no longer the one
            # in hand, and the lookup finds nothing.
            given = known
            if term in known \
                    and requirement(line) in getattr(known[term], 'origin', ()):
                continue
            if term in known and not self.rests_on_lines(how):
                given = {k: v for k, v in known.items() if k != term}
            self.supplying.add(term)
            try:
                made = self.side(want, how, scope, given, step)
            finally:
                self.supplying.discard(term)
            if not declined(made):
                made = self.discharged_by(made, step, how, line)
            known[term] = made
        return known

    def rests_on_lines(self, how):
        """Whether a `requires` line's reason is the lines it cites.

        `from H1` is, and so is a definition the database gives no target
        for, which the notation folds into the line it is unfolded at.
        """
        reason = how.strip().split(',')[0].strip()
        if reason.startswith('from '):
            return True
        kind, _, name = reason.partition(':')
        if kind != 'def' or not name.strip():
            return False
        item = self.items.get(resolve(name.split()[0], self.thm.module))
        return item is not None and item.kind == 'definition' \
            and not targets.clauses(item)

    def unfolded_at(self, term, scope, facts, refs):
        """What a line a `requires` line names says, taken apart.

        A definition the database gives no target for is one the notation
        folds away, so there is nothing in the library to cite and the
        unfolding is the line itself: `A, B, C form a triangle` is four
        claims conjoined, and a line asking for one of them is asking for a
        conjunct of the line it names. A `from H1` reason asks the same of
        the line it names, with no definition between.
        """
        for ref in refs:
            line = self.lines.get(ref)
            if line is None:
                continue
            held = {line.term: self.carried(ref, facts, self.lines)}
            self.unpack(line.term, held[line.term], scope, held)
            if term in held:
                return held[term]
            # Or what a membership it states says as well: `let k ∈ ℕ`
            # says k ∈ ℝ and k ≠ 0 (`SYNTAX.md`), each one lemma from it.
            # An obtain's names have their membership in the scope, with the
            # line as its origin, as below.
            stated = dict(held)
            for said, proof in facts.items():
                if getattr(proof, 'origin', None) == {ref}:
                    stated.setdefault(said, proof)
            for said, proof in stated.items():
                more = self.implied(said, proof, scope)
                if term in more:
                    return more[term]
            # The line with its own letters bound: a `fix` elsewhere took n,
            # so line 5 of the triangular reciprocals binds g where the
            # requires line citing it writes n. One claim, spelt apart.
            if self.to_term(line.term).label in rules.BOUND:
                spelt = self.respelt(held[line.term], line.term, term, scope)
                if spelt is not None:
                    return spelt
            # What the line says beyond its recorded term: an obtain records
            # the body it obtained, and `c ∈ ℝ` went into the scope when the
            # name's domain was assumed. Its origin is the line, and that is
            # what makes it the line's to give.
            found = facts.get(term)
            if found is not None and getattr(found, 'origin', None) == {ref}:
                return found
        return Declined('no line this names says it')

    def side(self, want, how, scope, facts, step=None):
        """A proof of what one `requires` line asks for.

        A `requires` line may name the lines it rests on, and a method that
        is not expanded has to say so. `requires q ≠ 0: inequalities, from
        3.1` asks only that a positive number is not zero; an assumption
        that drops the 3.1 asks that the number is not zero, which is more
        than the line says and leaves 3.1 unused.
        """
        # While the line is proved, what it cites is what may be carried
        # without a search, and what the search is offered is what the line
        # may rest on.
        citing, self.citing = self.citing, frozenset(citations(how))
        allowed = None if step is None else self.reason_allows(step, how)
        try:
            with self.resting_on(allowed):
                return self.by_its_reason(want, how, scope, facts, step)
        finally:
            self.citing = citing

    def by_its_reason(self, want, how, scope, facts, step=None):
        """`side`, with what the line cites in hand."""
        term = self.term(want)
        # Read from the lines it cites before the scope is asked, since the
        # scope may hold the same claim for another reason.
        if self.rests_on_lines(how):
            found = self.unfolded_at(term, scope, facts, citations(how))
            if declined(found):
                raise self.defect(self.at,
                                  f'{how.strip()} does not reach '
                                  f'{self.render(term)}, which this line '
                                  f'claims it supplies')
            return found
        if term in facts:
            return facts[term]
        closure = how.strip().split(',')[0].strip()
        # `membership` builds the fact from its parts, as a step naming it
        # does, from the lines this one cites (`METHODS.md`).
        if closure == 'membership':
            made = self.member_of(self.to_term(term), scope, facts, step)
            if declined(made):
                raise self.defect(self.at, f'{self.render(term)} is not '
                                           f'built from what the requires '
                                           f'line cites: {made}')
            return made
        # A line naming a method is discharged by the method it names. A
        # closed numeral inequality is what `arithmetic` decides outright,
        # and a declared lemma reaching the same fact reaches it the long
        # way round: 1 < 2 through membership of ℤ≥2 costs five lemmas.
        if closure == 'arithmetic':
            # Said in the page's words where the line is in hand, as a
            # step's claim is.
            written = next((fact for fact, _how, _no in
                            (step.requires if step is not None else ())
                            if self.claim_of(fact) == term), None)
            said = (f'the requires line of step {fmt(step.number)} claims '
                    f'{written.strip()}' if written is not None
                    else f'the requires line {self.render(term)}')
            self.worked_out(term, said)
            found = self.prove_numeral(term, scope, facts)
            if not declined(found):
                return found
        # A line naming an item is that item cited, the same as a step
        # naming it. `GOALS.md` decision 9 is why this stands before the
        # routes below: the readable text is canonical and the kernel proof
        # is derived from it, so what the line says supplies the fact is
        # what supplies it, and not whatever `rules.MEMBERSHIP` reaches.
        #
        # Only where the item has a target. Citing one without is assuming
        # it, and the lists at the head of each elaborated file are what
        # `GEOMETRY.md` measures the corpus by.
        #
        # The name ends at the first space, because what follows it is the
        # instantiation: `thm:stdlib/numbers/abs-real x := a, from H1` names
        # `stdlib/numbers/abs-real` and not `stdlib/numbers/abs-real x := a`.
        if step is not None and closure.split(':', 1)[0] in ('thm', 'def'):
            item = self.items.get(resolve(closure.split(':', 1)[1].split()[0],
                                          self.thm.module))
            if item is not None and targets.clauses(item):
                return self.cite_item(step, term, scope, facts, item, how)
        if closure == 'arithmetic':
            # A value is the other thing `arithmetic` decides, and a closed
            # one is an identity of the field with no atoms in it, so it
            # goes where identities go rather than wanting a second
            # procedure. `METHODS.md` lists the two as one method, so both
            # halves are tried before anything generic: a line naming the
            # method and reaching it through `settle` instead is the method
            # not being asked rather than the method failing.
            found = self.prove_field(None, term, scope, facts, self.lines)
            if not declined(found):
                return found
            raise self.unshown(term, f'the requires line '
                                     f'{self.render(term)}')
        if closure == 'inequalities':
            # A side condition resting on a method is proved the way a step
            # resting on it is, where the method can prove one at all.
            found = self.prove_order(citations(how), term, scope, facts,
                                     self.lines)
            if not declined(found):
                return found
        # Nothing generic stands here. A route that settles the claim from
        # wherever the scope holds it rests the proof on something other than
        # the reason the line gives, and the file still verifies, so nothing
        # would show it. What is left is a method saying at the head of the
        # file that it was not expanded, or an error naming the line.
        if closure in ('inequalities', 'algebra'):
            # A side condition resting on a closure method rests on it the
            # same way a step does, and is listed the same way: under what
            # the line cites, and under nothing else. `arithmetic` is not
            # among them: it is reported above where it cannot prove.
            asks = [(self.lines[ref].term,
                     self.carried(ref, facts, self.lines))
                    for ref in citations(how) if ref in self.lines]
            statement = term
            for one, _given in reversed(asks):
                statement = self.seq(one, statement, 'wi')
            proof = self.stated(closure[:3], '|- ' + self.render(statement))
            if not asks:
                return self.seq(term, scope, proof, 'a1i')
            for i, (one, given) in enumerate(asks):
                rest = term
                for later, _p in reversed(asks[i + 1:]):
                    rest = self.seq(later, rest, 'wi')
                proof = self.seq(scope, one, rest, given, proof,
                            'syl' if i == 0 else 'mpd')
            return proof
        raise self.defect(self.at,
                          f'{how.strip()} does not reach '
                          f'{self.render(term)}, which this line claims '
                          f'it supplies')

    def required(self, step, goal, want, scope, facts):
        """The `requires` line that supplies one side condition.

        A lemma can ask for more than the text writes: `divides` wants both
        sides of `d || n` in ZZ, and only the side a reader could doubt is
        written down. What no line supplies is settled from the term.
        """
        written = {self.term(self.read(t)) for t, _h, _l in step.requires}
        # The scope's copy of a claim is taken only where no line of the
        # step writes it: `let x ∈ ℤ` and `requires x ∈ ℤ: from K1` are one
        # claim, and the step names the second.
        if goal in facts and goal not in written:
            return facts[goal]
        # A lemma may ask its side conditions as one conjunction where the
        # text writes a line each: `divides` wants ( M e. ZZ /\ N e. ZZ )
        # and the step says `requires d ∈ ℤ` and `requires c ∈ ℤ`. Asking
        # whether the whole goal is what a line says misses both, so a
        # conjunction the lines do name between them is answered a part at
        # a time. Only then: a conjunction no line touches is left to the
        # route below, which is what proved it before.
        whole = self.to_term(goal)
        if any(one.rpn(self.flabel) in written for one in whole.children):
            joined = self.conjoined(
                whole, scope,
                lambda one: self.required(step, one.rpn(self.flabel), want,
                                          scope, facts))
            # Each part raises where its line does not reach it, so what
            # comes back is never a decline; asked all the same, because a
            # caller of this takes what it gives as a proof.
            if declined(joined):
                raise self.defect(self.at, f'{joined}')
            if joined is not None:
                return joined
        for text, how, line in step.requires:
            node = self.read(text)
            if self.term(node) == goal:
                # `side` is where a line is discharged by what it names, so
                # it is given `how` as well as the claim. A route reading
                # only the claim settles it from whatever the scope holds,
                # which is the proof not resting on the reason the page
                # gave.
                made = self.side(node, how, scope, facts, step)
                # A line that is there and whose justification does not
                # reach it is the text's to fix in the same way one that is
                # missing is. Handing the decline to the caller would put it
                # in a proof join, and say nothing about the line at fault.
                if declined(made):
                    raise self.defect(
                        self.at,
                        f'the requires line for {self.render(goal)} is '
                        f'justified by {how}, which does not reach it: {made}')
                return self.discharged_by(made, step, how, line)
        # A `requires` line that is not there is the text's to fix, so this
        # one is a defect. What it is built from declining is not, which is
        # why only a decline is turned into one here.
        found = self.settle(self.to_term(goal), scope, facts)
        if declined(found):
            raise self.defect(
                self.at, f'no requires line for {self.render(goal)}')
        return found

    def unproved_requires(self):
        """The `requires` lines of this theorem never proved from their reasons.

        A `requires` line is where a step writes a side condition and why it
        holds, and each is proved from that reason once, when its step
        starts, and checked then to rest on nothing else. A line never
        proved is one whose reason nothing checked: what it says may have
        been reached some other way, or not been needed, and either way the
        page's justification went unread. Every line of every step, whatever
        it cites.
        """
        return sorted(line for step in self.thm.steps
                      for _text, _how, line in step.requires
                      if requirement(line) not in self.rests_on)
