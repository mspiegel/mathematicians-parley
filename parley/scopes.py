"""Scopes: the context each line of a proof is proved under.

This is the second of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given the blocks, hypotheses, cases and `define` lines,
it produces the context each line is proved under, carries a fact into an
inner scope, and closes a block into the claim it owns. This is working in
deduction form, and the section on scopes in `ELABORATION.md` describes it.

Every scope is a conjunction of what has been assumed, and `frames` keeps one
entry per assumption: the scope with it conjoined, the assumption, and what
was known there. A step whose lemma forbids an inner assumption is proved at
an outer frame and carried back in.
"""
import contextlib
import re

import kernel
import rules
from match import instantiation
from parse import CITED, Declined, declined
from reading import hypothesis_body
from spell import seq


class Fact:
    """A claim, a proof of it at one scope, and the sentences it was read from.

    A line may say several things, and a substitution may land in one of
    them, so what is kept is every sentence rather than the claim as one
    tree. A line read from no text at all keeps none.
    """

    def __init__(self, term, proof, sentences=()):
        self.term, self.proof, self.sentences = term, proof, sentences


class Block:
    """A block being elaborated: what it opened over and what it opened."""

    def __init__(self, owner, outer, facts, frame):
        self.owner, self.outer, self.outside = owner, outer, facts
        self.frame = frame          # index into the scope frames
        self.scope, self.facts = outer, facts
        self.supposed = None        # contradiction
        self.over = self.base = None                      # induction
        self.variable = None        # the setvar a fix introduced
        self.named = None           # the names in hand before it opened
        self.bound = None           # and which variable each binder had
        self.inner = None           # and which each had while it was open
        self.assumed = {}           # cases: part number -> what it assumes
        self.entered = None         # cases: the part now open
        self.case_opened_at = None  # cases: the closers before that part
        self.claim = self.proof = None
        self.parts = {}             # part number -> the last fact in it


class Scopes:
    def open_outermost(self, scope, facts):
        """The first frame: the theorem's hypotheses, and what they say."""
        self.frames = [(scope, None, facts)]

    @contextlib.contextmanager
    def frames_kept(self):
        """The frames as they stand, given back when the block of code ends.

        A route that widens the scope to prove something under a binder or
        a case — a membership `ralrimiva` gives back, each side of a split —
        owns the frames it pushes and nothing else does. A frame left
        standing is offered to whatever is proved next, and a lemma once
        stated its hypothesis under a binder's membership that way, which
        mmverify caught.
        """
        frame = len(self.frames)
        try:
            yield
        finally:
            del self.frames[frame:]

    def widen(self, scope, facts, added, origin=None):
        """Conjoin one more thing onto the antecedent, carrying the facts.

        This is what every block form does when it opens: `ELABORATION.md`
        requirement 1. The frame is kept so that a step whose lemma forbids
        the innermost assumption can be proved without it.

        `origin` is what on the page the assumption is, where it is on the
        page at all. A block's supposition is; the membership of a variable
        a binder introduces while its body is read is not, and has none.
        """
        inner = seq(scope, added, 'wa')
        lifted = {k: self.seq(inner, scope, k,
                              self.seq(scope, added, 'simpl'), v, 'syl')
                  for k, v in facts.items()}
        lifted[added] = self.seq(scope, added, 'simpr')
        if origin is not None:
            lifted[added] = self.seal(lifted[added], origin)
        self.unpack(added, lifted[added], inner, lifted)
        # Each frame keeps what is known at it, because a step whose lemma
        # forbids an inner assumption is proved at an outer one.
        self.frames.append((inner, added, lifted))
        return inner, lifted

    def lifted_to(self, claim, proof, at, scope):
        """A proof made under `at`, said under `scope`, if `scope` is `at`
        widened; None otherwise.

        Every widening conjoins one assumption onto the antecedent, so a
        scope opened inside another reads back as that one with each added
        assumption hanging off it, and the proof is carried in the way
        `widen` carries every fact: one `simpl` and `syl` per assumption.
        A scope that is not a widening of `at` — one a step was hoisted to —
        gives None, and the proof made under `at` is not offered there.
        """
        if at == scope:
            return proof
        chain, node = [], self.to_term(scope)
        while node.variable is None and node.label == 'wa' \
                and len(node.children) == 2:
            outer, added = node.children
            chain.append(added.rpn(self.flabel))
            if outer.rpn(self.flabel) == at:
                break
            node = outer
        else:
            return None
        here = at
        for added in reversed(chain):
            inner = self.seq(here, added, 'wa')
            proof = self.seq(inner, here, claim, self.seq(here, added, 'simpl'), proof,
                        'syl')
            here = inner
        return proof if here == scope else None

    def conjoined(self, wanted, scope, answer):
        """A conjunctive goal, from whatever answers each of its parts.

        Both places that reach a conjunction want the same three moves —
        take the parts, answer each, join what comes back — and differ only
        in what answering is: `settle` proves a part from the scope, and
        `required` reads the line the step wrote for it. So the moves are
        here and the answering is the caller's.

        None where the goal is not one of these shapes, which is not a
        decline: the caller has its own way on and this had no opinion.
        """
        if wanted.label not in rules.JOIN:
            return None
        under = [answer(one) for one in wanted.children]
        for one in under:
            if declined(one):
                return one
        return self.seq(scope, *(one.rpn(self.flabel) for one in wanted.children),
                   *under, rules.JOIN[wanted.label])

    def unpack(self, term, proof, scope, facts, depth=4):
        """Record each conjunct of a fact as a fact of its own."""
        if depth <= 0:
            return
        node = self.to_term(term)
        picks = rules.SPLIT.get(node.label)
        if not picks or len(picks) != len(node.children):
            return
        kids = [c.rpn(self.flabel) for c in node.children]
        for part, pick in zip(kids, picks, strict=True):
            if part in facts:
                continue
            facts[part] = self.seq(scope, term, part, proof, *kids, pick, 'syl')
            self.unpack(part, facts[part], scope, facts, depth - 1)

    def open_block(self, step, scope, facts, lines):
        """A block's assumption is conjoined onto the antecedent.

        All four block forms do this; what differs is the lemma that closes
        them. `ELABORATION.md` requirement 1.
        """
        head = step.just.head
        block = Block(step, scope, facts, len(self.frames) - 1)
        # Taken before the block names anything, so that what it names is
        # what closing it gives back.
        block.named, block.bound = dict(self.names), dict(self.bound_as)
        if head == 'contradiction':
            kind, text, label, _l, _p = step.openers[0]
            node = self.read(hypothesis_body(kind, text))
            block.supposed = self.term(node)
            block.scope, block.facts = self.widen(
                scope, facts, block.supposed, self.assumption(block, label))
            if label:
                lines[label] = Fact(block.supposed,
                                    block.facts[block.supposed], (node,))
            self.joined = None
        elif head == 'fix':
            block.scope, block.facts = scope, facts
            for kind, text, label, _l, _p in step.openers:
                body = hypothesis_body(kind, text)
                if kind == 'let':
                    # A fixed name is a variable of the kernel, not a class,
                    # and it must avoid whatever the notations bind: the sum
                    # binds `k`, so a proof that fixes `k` cannot use it.
                    node = self.read(body)
                    name = self.subject_of(node).text
                    block.variable = self.fixed_var(name, block.scope)
                    self.names[name] = f'{block.variable} cv'
                    # `let X be a set` fixes a name over nothing and says
                    # only that it is a set, so there is no set to record,
                    # the same way `hypotheses` reads it at the head.
                    if node.notation == 'membership':
                        self.sets[name] = self.term(node.children[1])
                node = self.read(body)
                added = self.term(node)
                block.scope, block.facts = self.widen(
                    block.scope, block.facts, added,
                    self.assumption(block, label))
                if label:
                    lines[label] = Fact(added, block.facts[added], (node,))
        elif head == 'cases':
            # Every other block opens one scope for all its children. A
            # `cases` opens one per part, so nothing is widened here and the
            # part is entered when its first child arrives.
            block.scope, block.facts = scope, facts
            block.assumed = {}
            for kind, text, label, _l, part in step.openers:
                body = hypothesis_body(kind, text)
                block.assumed[part] = (self.read(body), label)
        elif head == 'induction':
            block.scope, block.facts = scope, facts
            block.over = re.search(r'induction on (\S+)',
                                   step.just.text).group(1)
            block.base = self.spare_var()
            # The step part fixes a name of its own, and `nn0indd` wants
            # that one apart from this: its letter would otherwise be taken
            # as its own even when it is this spare, as the ten-power proof's
            # m was, and the two were one variable.
            self.taken.add(block.base)
        else:
            raise self.defect(step.line,
                              f'no expansion for a {head} block')
        return block

    @staticmethod
    def assumption(block, label):
        """What on the page a block's assumption is.

        Its label where the text gives one. Where it does not, the block's
        own step, since that is where a reader finds it; an assumption with
        no name is still something the page says, and a proof resting on it
        rests on the page rather than on nothing.
        """
        if label:
            return label
        return '.'.join(str(p) for p in block.owner.number) + ' assumes'

    def enter_case(self, block, part, lines):
        """Open the scope one case of a `cases` block runs under."""
        if block.entered == part:
            return block.scope, block.facts
        del self.frames[block.frame + 1:]
        # A case gives back what it named, the way the block does when it
        # closes: the next one starts from where the block started, and the
        # assumption below is read against that and not against whatever
        # the case before it left behind.
        self.names = dict(block.named)
        node, label = block.assumed[part]
        assumed = self.term(node)
        block.scope, block.facts = self.widen(block.outer, block.outside,
                                              assumed,
                                              self.assumption(block, label))
        block.entered = part
        if label:
            lines[label] = Fact(assumed, block.facts[assumed], (node,))
        return block.scope, block.facts

    @staticmethod
    def end_case(block, closers):
        """The closers an obtain raised inside a case, spent where it ends.

        The lemma that closes the cases wants each case over the scope the
        case opened, and an obtain inside one widens that: the first case
        of the intermediate value proof obtains δ and then x₁. So what the
        case ends on is discharged of them, as a contradiction's claim is.
        """
        if block.case_opened_at is None:
            return closers
        inside = closers[block.case_opened_at:]
        if inside and block.entered in block.parts:
            claim, proof, _where = block.parts[block.entered]
            for close in reversed(inside):
                proof = close(proof, claim)
            block.parts[block.entered] = (claim, proof, block.scope)
        return closers[:block.case_opened_at]

    @staticmethod
    def hand_up(done, blocks):
        """A closed block is the result of the part of its parent it sits in.

        What it was proved under goes up with it, because a part's claim is
        written inside the part and what reads it stands outside.
        """
        if done.owner.part is not None and blocks:
            blocks[-1].parts[done.owner.part] = (done.claim, done.proof,
                                                 done.outer)
            if done.variable:
                blocks[-1].variable = done.variable

    def close_block(self, block, facts, lines, closers, deep):
        """What a block gives back, by the lemma its kind closes with.

        An `obtain` inside a block does not discharge where the proof ends:
        it discharges where the block does, since the lemma that closes the
        block wants what the block holds and not what the obtain's scope
        holds. So the closers raised inside a contradiction are spent on it,
        and only what is left over reaches the end of the proof.
        """
        step = block.owner
        head = step.just.head
        inside = closers[block.opened_at:]
        # A block gives back its scope and its names together: the frames it
        # pushed, and whatever it fixed, obtained or defined inside. The
        # word a fixed name took goes back with them, so an enclosing block
        # that binds the same word still means what it meant.
        block.inner = dict(self.bound_as)
        del self.frames[block.frame + 1:]
        self.names, self.bound_as = dict(block.named), dict(block.bound)
        if head == 'contradiction':
            block.claim, block.proof = self.close_contradiction(
                block, facts, inside, deep, lines)
            closers = closers[:block.opened_at]
        elif head == 'fix':
            held = lines[self.last]
            # A fix is a generalisation: it fixed a name, said something
            # about it, and the block claims that of every such name. It
            # closes the same way wherever it stands, including as a part
            # of an induction — what `nn0indd` wants of its step is not
            # what the block claims, and turning one into the other is
            # `close_induction`'s, since that is what knows the lemma.
            block.claim, block.proof = self.close_fix(block, held, inside)
            closers = closers[:block.opened_at]
        elif head == 'cases':
            closers = self.end_case(block, closers)
            block.claim, block.proof = self.close_cases(block, lines)
        elif head == 'induction':
            block.claim, block.proof = self.close_induction(block, lines)
        number = '.'.join(str(p) for p in step.number)
        block.proof = self.check_step(block.proof, step, number, block=True)
        outer = dict(block.outside)
        outer[block.claim] = block.proof
        lines[number] = Fact(block.claim, block.proof)
        self.last = number
        return block.outer, outer, closers

    def close_contradiction(self, block, facts, inside, deep, lines):
        """A contradiction closes on the pair its `join` named.

        The contradiction is struck where the two lines are, and only then
        is anything discharged: the pair 3.16 and 3.1 names p and q, and an
        existential over p and q cannot be discharged around a claim that
        still mentions them. So pm2.21dd takes the pair to the block's claim
        first, the obtains raised inside the block discharge that, and the
        supposition is dropped last. The join itself emits nothing: this
        consumes both lines.

        Which lemma drops the supposition depends on which of the two is
        the negation. Supposing √2 rational to show it is not is pm2.01d;
        supposing p is not above n to show that it is, as the primes proof
        does, is pm2.18d and reaches the claim itself rather than a double
        negation of it.

        A joined line may say several things at once — 3.1 names p and q and
        says in the same breath that nothing above 1 divides both — so the
        pair is looked for among the parts of the two lines rather than
        between the lines whole.
        """
        step, scope, supposed = block.owner, block.outer, block.supposed
        if not self.joined:
            raise self.defect(step.line, 'the block closes on no join')
        held = lines.get(self.last)
        found = self.opposing([*self.joined,
                               *([held.term] if held else [])], facts, deep)
        if found is None:
            raise self.defect(step.line,
                              'the joined lines are not a contradiction')
        first, second, known = found
        claim = self.claim_of(' '.join(step.claim))
        proof = self.seq(deep, first, claim, known[first], known[second],
                    'pm2.21dd')
        for close in reversed(inside):
            proof = close(proof, claim)
        lifted = self.seq(scope, supposed, claim, proof, 'ex')
        if claim == self.seq(supposed, 'wn'):
            return claim, self.seq(scope, supposed, lifted, 'pm2.01d')
        if supposed == self.seq(claim, 'wn'):
            return claim, self.seq(scope, claim, lifted, 'pm2.18d')
        raise self.defect(step.line,
                          'the block claims neither its supposition negated '
                          'nor what its supposition denies')

    def opposing(self, lines, facts, scope):
        """A claim and its negation, among the parts of what the block holds.

        What holds the pair differs by proof: the √2 proof joins two lines
        that each say one thing, and Cantor's cases give back a single line
        saying both. So every part of every line offered is a candidate, and
        a line saying several things is taken apart first.
        """
        known = dict(facts)
        for line in lines:
            if line in known:
                self.unpack(line, known[line], scope, known)
        seen = [t for line in lines for t in self.parts(line) if t in known]
        for one in seen:
            for other in seen:
                if other == self.seq(one, 'wn'):
                    return one, other, known
        return None

    def parts(self, term):
        """A fact and every conjunct inside it, the whole one first."""
        yield term
        node = self.to_term(term)
        picks = rules.SPLIT.get(node.label)
        if picks and len(picks) == len(node.children):
            for child in node.children:
                yield from self.parts(child.rpn(self.flabel))

    def close_fix(self, block, held, inside=()):
        """A fix closed by giving back everything it took.

        `ralrimiva` wants what was proved under a fixed name, said out of
        the scope the block opened over, and `ex` does the same for what
        the block assumed. `db/methods.records` names both, and a fix may
        take several names before it assumes: Bezout's step 10 fixes an x
        and a y and supposes their combination is a natural number.

        Which names, which sets and which supposition are read off the
        claim the block states, since that is what the text wrote, and they
        are peeled in the order the openers widened the scope. Putting them
        back runs the other way, innermost first, because that is the order
        each lemma can be applied in.

        A fix that is one part of an induction never arrives here:
        `close_block` hands that one over whole, for `nnind` to take.
        """
        step = block.owner
        # Read with the variables the block had, not the ones given back:
        # the claim quantifies the names the block fixed, and closing it
        # has already returned those words to whatever held them outside.
        kept, self.bound_as = self.bound_as, dict(block.inner)
        try:
            claim = self.claim_of(' '.join(step.claim))
        finally:
            self.bound_as = kept
        layers, rest = [], self.to_term(claim)
        for kind, _text, _label, _line, _part in step.openers:
            if kind == 'let' and rest.label == 'wral':
                body, variable, over = rest.children
                layers.append(('ralrimiva', variable.rpn(self.flabel),
                               over.rpn(self.flabel)))
                rest = body
            elif kind == 'let' and rest.label == 'wal':
                # `let X be a set` fixes a name over nothing, so the claim
                # says its body of every set there is and `alrimiv` gives
                # that back. `db/methods.records` names it beside the other.
                layers.append(('alrimiv',
                               rest.children[1].rpn(self.flabel), None))
                rest = rest.children[0]
            elif kind == 'assume' and rest.label == 'wi':
                layers.append(('ex', rest.children[0].rpn(self.flabel), None))
                rest = rest.children[1]
            elif kind == 'let':
                raise self.defect(
                    step.line, 'a fix that claims nothing of every such name')
            else:
                raise self.defect(
                    step.line, 'a fix whose claim supposes nothing where the '
                    'block assumes')
        # The scope each layer was taken at, which is what it is given back
        # to. `widen` conjoined them on the way in and these are the same
        # terms read off the claim.
        scopes, scope = [], block.outer
        for how, what, over in layers:
            scopes.append(scope)
            if how == 'ex':
                scope = self.seq(scope, what, 'wa')
            else:
                scope = self.seq(scope, self.seq(f'{what} cv', over or 'cvv', 'wcel'),
                            'wa')

        # An `obtain` inside the block widened the scope past what the
        # openers widened it to, and discharges where the block does, not
        # where the proof ends — the same as inside a contradiction. So the
        # closers it raised are spent before anything is generalised, and
        # what is left stands at the scope the openers made.
        proof, said = held.proof, held.term
        for close in reversed(inside):
            proof = close(proof, said)
        # The last line and the claim are written in different places, so a
        # name bound in both may be spelt two ways: the subsets induction's
        # step states what its own last line states, and that line was
        # written where the word was already taken.
        want = rest.rpn(self.flabel)
        proof = self.respelt(proof, said, want, scope)
        if proof is None:
            raise self.defect(step.line,
                              'the block does not reach what it claims of '
                              'the name it fixed')
        said = want
        for (how, what, over), outer in zip(reversed(layers),
                                            reversed(scopes), strict=True):
            if how == 'ex':
                proof = self.seq(outer, what, said, proof, 'ex')
                said = self.seq(what, said, 'wi')
            elif how == 'alrimiv':
                # `let X be a set` says X ∈ _V and the claim quantifies X
                # over nothing, so that membership is dropped before the
                # name is given back: every setvar is a set, which is `vex`.
                member = self.seq(f'{what} cv', 'cvv', 'wcel')
                proof = self.seq(outer, member, said, self.ap('vex', {'x': what}),
                            proof, 'mpan2')
                proof = self.seq(outer, said, what, proof, 'alrimiv')
                said = self.seq(said, what, 'wal')
            else:
                proof = self.seq(outer, said, what, over, proof, 'ralrimiva')
                said = self.seq(said, what, over, 'wral')
        return claim, proof

    def close_cases(self, block, lines):
        """The cases and the disjunction that says one of them holds.

        mpjaodan wants each case as an implication out of the scope with its
        own assumption conjoined, which is what each part was proved as, and
        the disjunction the block cites. The fourth and last block form, and
        the same shape as the other three: widen, prove, close with one
        lemma.

        More than two cases follow the disjunction, which is built from the
        left: `f(c) < 0 or f(c) = 0 or 0 < f(c)` is the first two or'd, then
        the third. `jaodan` makes one case of the first two, over their
        disjunction, and so on down, and `mpjaodan` closes on the last.
        """
        step, scope = block.owner, block.outer
        if set(block.parts) != set(block.assumed):
            raise self.defect(step.line, 'a case of the block proves nothing')
        claim = self.claim_of(' '.join(step.claim))
        parts = sorted(block.assumed)
        assumed = [self.term(block.assumed[p][0]) for p in parts]
        said = [block.parts[p][1] for p in parts]
        which, proof = assumed[0], said[0]
        for one, shown in zip(assumed[1:-1], said[1:-1], strict=True):
            proof = self.ap('jaodan', {'ph': scope, 'ps': which, 'ch': claim,
                                       'th': one}, proof, shown)
            which = seq(which, one, 'wo')
        disjunction = self.carried(step.just.refs[0], block.outside, lines)
        if seq(which, assumed[-1], 'wo') != self.lines[step.just.refs[0]].term:
            raise self.defect(step.line, 'the cases are not the disjunction '
                                         'the block cites, taken in order')
        return claim, self.ap('mpjaodan', {'ph': scope, 'ps': which,
                                           'ch': claim, 'th': assumed[-1]},
                              proof, said[-1], disjunction)

    def close_induction(self, block, lines):
        """Induction closes with the lemma for the set it runs over.

        Whichever it is wants the claim five ways and the text writes none
        of them: it says only which name to induct on and where to start. So
        the claim is read as a function of that name and instantiated, and
        each instance is tied to the general one by congruence.
        `ELABORATION.md` requirement 13.
        """
        step, scope = block.owner, block.outer
        if set(block.parts) != {0, 1}:
            raise self.defect(step.line, 'induction wants a base and a step')
        (base_claim, base, beneath), (step_claim, stepped, under) = (
            block.parts[0], block.parts[1])
        name, general = block.over, f'{block.base} cv'
        over = self.sets.get(name)
        if over not in rules.INDUCTION:
            raise self.defect(step.line,
                              f'nothing here inducts over {self.render(over)}'
                              if over else
                              f'nothing says what {name} runs over')
        lemma, begins = rules.INDUCTION[over]
        at = re.search(r'starting at ([^\s,]+)', step.just.text)
        start = self.term(self.read(at.group(1))) if at else begins
        if start != begins:
            raise self.defect(step.line,
                              f'an induction over {self.render(over)} starts '
                              f'at {self.render(begins)}, and the text says '
                              f'{self.render(start)}')
        variable = block.variable or self.spare_var()
        next_one = self.seq(f'{variable} cv', 'c1', 'caddc', 'co')

        with self.names_kept():
            self.names[name] = general
            # Read as a sentence, so that a claim written as prose ends where
            # a reader ends it: the subsets proof inducts on `For every set
            # X, if |X| = n then |𝒫X| = 2^n.`, and the stop is not part of
            # the claim.
            said = self.sentences(' '.join(step.claim))
            pattern = self.freeze(self.read(said[0] if len(said) == 1
                                            else ' '.join(step.claim)))
        shapes = [start, f'{variable} cv', next_one, self.names[name]]
        instances, ties = [], []
        for value in shapes:
            here = self.seq(general, value, 'wceq')
            made = self.rewrite(pattern, general, value, here,
                                self.seq(here, 'id'))
            if declined(made):
                raise self.defect(step.line,
                                  f'the claim is not about the induction '
                                  f'variable: {made}')
            built, proof = made
            instances.append(built)
            ties.append(proof)
        claimed, held, reached, whole = instances
        member = self.seq(self.names[name], self.sets[name], 'wcel')
        body = self.term(pattern)

        # A part gives back what it claims, and what a `fix` claims is a
        # universal. `nn0indd` asks its step as a deduction — the name and
        # the instance conjoined onto the scope — so the one is turned into
        # the other here, which is where the lemma is known.
        #
        # A part's claim is written inside the part, where a word may
        # already be taken by what the part assumes, so the subsets
        # induction's parts bind a set the pattern binds under another
        # letter. The same claim, and `respelt` says so. The step is put
        # into the lemma's spelling while it is still a universal, because
        # afterwards its hypothesis is in the scope, where a claim cannot
        # be respelt.
        taken = self.to_term(step_claim)
        if taken.label == 'wral' and taken.children[0].label == 'wi':
            says = self.seq(held, reached, 'wi')
            stepped = self.respelt(stepped, step_claim,
                                   self.seq(says, variable, over, 'wral'), under)
            if stepped is None:
                raise self.defect(step.line,
                                  'the step does not reach the next instance')
            inner = self.seq(under, self.seq(f'{variable} cv', over, 'wcel'), 'wa')
            stepped = self.seq(under, says, variable, over, stepped, 'r19.21bi')
            stepped = self.seq(inner, held, reached, stepped, 'imp')
            step_claim, under = reached, self.seq(inner, held, 'wa')

        base = self.respelt(base, base_claim, claimed, beneath)
        stepped = self.respelt(stepped, step_claim, reached, under)
        if stepped is None:
            raise self.defect(step.line,
                              'the step does not reach the next instance')
        if base is None:
            raise self.defect(step.line,
                              'the base does not reach the first instance')
        run = self.seq(scope, body, claimed, held, reached, whole,
                  block.base, variable, self.names[name], *ties, base,
                  stepped, lemma)
        # The lemma states the membership apart from the rest of the
        # antecedent, and the scope already holds it, so the two are
        # conjoined back.
        if member not in block.outside:
            raise self.defect(step.line,
                              f'nothing in scope says {member}')
        return whole, self.seq(scope, self.seq(scope, member, 'wa'), whole,
                          self.seq(scope, scope, member, self.seq(scope, 'id'),
                              block.outside[member], 'jca'),
                          run, 'syl')

    def obtain(self, step, number, scope, facts, lines, closers):
        """Names introduced from an existence claim, which opens a scope.

        This is the step that changes the shape of every step after it. The
        kernel cannot hand a name out of an existential, so everything below
        is proved as the body of an implication and the existential is
        discharged at the very end.

        The claim may come from a definition unfolded, or from a theorem that
        states one outright, and it may introduce more than one name at once:
        `thm:proof/sqrt2-irrational/lowest-terms` gives a numerator and a
        denominator together.
        """
        got = [n.strip() for n in re.match(
            r'obtain\s+(.+?)(?::|\s+from\b)', step.just.text).group(1)
            .split(',')]
        # Spelt as `parse.CITED` spells an item and not as a run of anything
        # that is not a space: an obtain writing no instantiation puts a
        # comma straight after the name, and it is not part of it.
        named = re.search(rf'\b((?:def|thm):{CITED})', step.just.text)
        if named is None:
            # The line already claims the existence, so there is no item to
            # instantiate and nothing of its own to rename. `SYNTAX.md` says
            # to prefer this form, because the other writes a name into a
            # claim standing above the justification that introduces it,
            # which is the one place in this language where a name is used
            # before the line that names it.
            where = step.just.refs[0] if step.just.refs else None
            held = lines.get(where) if where else None
            if held is None:
                raise self.defect(step.line,
                                  'an obtain that names neither an item nor '
                                  'a line claiming the existence')
            ex, p_ex = held.term, self.carried(where, facts, lines)
            # Eliminating an existential puts the name it binds into the
            # scope, and the lemma that does it forbids that name in what
            # the scope already says. A `contradiction` supposing an
            # existence is such a scope: the supposition is the scope, and
            # it binds the very name being introduced. So the claim is
            # respelt first, over names nothing else holds.
            standing = {t for t in scope.split()
                        if t in self.sigs and self.sigs[t].kind == '$f'}
            if {self.flabel[v]
                    for v in self.bound_in(self.to_term(ex))} & standing:
                fresh = self.renamed(ex, len(got))
                apart = self.renaming(self.to_term(ex), self.to_term(fresh))
                if apart is None:
                    raise self.defect(step.line,
                                      'the existence this obtains from binds '
                                      'a name the scope already holds')
                p_ex = self.seq(scope, ex, fresh, p_ex,
                           self.seq(self.seq(ex, fresh, 'wb'), scope, apart, 'a1i'),
                           'mpbid')
                ex = fresh
        elif named.group(1).startswith('def:'):
            cites = step.just.text.split(':', 1)[1].strip()
            subject = self.names[instantiation(cites)[0][1]]
            # A fresh name, not the lemma's own: `divides` binds `n`, and a
            # proof that obtains from it twice would introduce one variable
            # for two different numbers.
            fresh = self.spare_var()
            with self.names_kept():
                lemma, var, kernel, _t, over, left = self.definition(
                    named.group(1), subject, var=fresh)
                body = self.term(kernel)
            ex = self.seq(body, var, over, 'wrex')
            made = self.unfolding(step, lemma, left, ex, var, over, scope,
                                  facts)
            if declined(made):
                raise self.defect(step.line, f'{lemma} does not unfold '
                                             f'what this obtains from')
            p_ex = self.seq(scope, left, ex, facts[left], made[0], 'mpbid')
        else:
            cites = step.just.text.split(':', 1)[1].strip()
            item = self.item_cited(named.group(1))
            with self.names_kept():
                for name, value in instantiation(cites):
                    self.names[name] = self.term(self.read(value))
                # A name is a variable of the kernel whatever it is spelt
                # with: `x₁` is no set.mm letter, and a spare stands for it
                # as one does for a binder's name.
                for name in got:
                    self.names[name] = f'{self.binder_var(name)} cv'
                ex = self.term(self.read(self.claimed_by(item)))
            # An item states its existential in its own names, and a binder
            # takes the variable its name is spelled with. The primes proof
            # obtains a p and concludes that there is a p, so the one it
            # obtains is renamed to a variable nothing else is holding.
            ex = self.renamed(ex, len(got))
            p_ex = self.cite_item(step, ex, scope, facts, item, cites)
        # What the line is obtained from is what it rests on; what it
        # introduces is sealed below with the same name, and rests on nothing.
        p_ex = self.check_step(p_ex, step, number)

        # The existential says which names it introduces and where they run,
        # so the scope is read off it rather than off the text.
        layers, rest = [], self.to_term(ex)
        while len(layers) < len(got):
            body_term, variable, over_term = rest.children
            layers.append((variable.rpn(self.flabel),
                           over_term.rpn(self.flabel)))
            rest = body_term
        body = rest.rpn(self.flabel)

        member = self.seq(*(self.seq(f'{v} cv', s, 'wcel') for v, s in layers))
        if len(layers) > 1:
            member = self.seq(member, 'wa')
        outer, held = self.widen(scope, facts, member, number)
        inner, lifted = self.widen(outer, held, body, number)

        for name, (variable, over_term) in zip(got, layers, strict=True):
            self.names[name] = f'{variable} cv'
            self.sets[name] = over_term
        # Read after the obtained names are bound, so a sentence naming one
        # of them is about the variable the existential introduced.
        lines[number] = Fact(body, lifted[body], self.said(step))

        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]

        def close(proof, goal):
            return self.seq(scope, ex, goal, p_ex,
                       self.seq(scope, body, goal, *pushed,
                           self.seq(outer, body, goal, proof, 'ex'), discharge),
                       'mpd')

        return inner, lifted, [*closers, close]

    def define(self, before, scope, facts, lines, closers):
        """Each `define` above line `before` as a name and its equation.

        A textbook's "let x₁ = min(b, c + δ/2)" introduces a number and says
        what it is, and the steps after it are about x₁. So a define is
        taken the way an `obtain` is: from `∃x x = E`, which `elisset` gives
        once E is a set, the scope is widened by `x = E` and the existential
        is discharged where the scope ends (`exlimdv`). Written out at every
        use instead, the min/max proof's bound put an `if` term into every
        inequality about x₁ and the calculators ran out of memory on it.

        The variable is a spare and never the name's own letter: Cantor
        defines a B and concludes that there is a B, and those are two sets.
        `definitions` keeps what each such variable stands for, so a lemma
        whose conclusion is written about the body can be fitted to a claim
        written about the name (`read_through`); the equation is held both
        ways round, so either side of a comparison may be the name.
        """
        for label, line, name, body in self.defined(before):
            self.at = line
            # A body naming an earlier define is held written out, so every
            # equation says in full what its name is: the subsets proof's T
            # is built over its U, and a lemma about T speaks of U's body.
            body = self.spelt_out(self.to_term(body)).rpn(self.flabel)
            var = self.spare_var()
            said = self.seq(f'{var} cv', body, 'wceq')
            ex = self.seq(said, var, 'wex')
            p_ex = self.apply_lemma('elisset', self.to_term(ex), scope, facts,
                                    None, crossing=False)
            if declined(p_ex):
                raise self.defect(line, f'cannot show that what {label} '
                                        f'names is a set: {p_ex}')
            outer, held = self.widen(scope, facts, said, label)
            turned = self.seq(body, f'{var} cv', 'wceq')
            held[turned] = self.seq(outer, f'{var} cv', body, held[said],
                                    'eqcomd')
            self.names[name] = f'{var} cv'
            self.definitions[var] = body
            lines[label] = Fact(said, held[said])

            def close(proof, goal, scope=scope, said=said, var=var, ex=ex,
                      p_ex=p_ex, line=line, label=label):
                # The claim discharged here was read before the define was,
                # so it cannot name the variable; `exlimdv` forbids it.
                if var in goal.split():
                    raise self.defect(line, f'what {label} names is still '
                                            f'named where its scope ends')
                return self.seq(scope, ex, goal, p_ex,
                                self.seq(scope, said, goal, var,
                                         self.seq(scope, said, goal, proof,
                                                  'ex'),
                                         'exlimdv'),
                                'mpd')

            scope, facts, closers = outer, held, [*closers, close]
        return scope, facts, closers

    def rebound(self, stated, claimed):
        """Whether two statements differ only in the letters they bind.

        An `obtain` renames what its existential binds, and a name the page
        defines is read with the proof's letters rather than the item's: the
        subsets proof's T binds `o` where `thm:proof/subsets/powerset-split-disjoint`'s
        own reading binds `u`. Those are one statement. A letter is bound
        where it stands directly under a constructor other than `cv`; every
        other letter must be the same on both sides.
        """
        pairs, binders = {}, set()

        def alike(one, two):
            if one.variable is not None or two.variable is not None:
                if one.variable is None or two.variable is None:
                    return False
                return pairs.setdefault(one.variable,
                                        two.variable) == two.variable
            if (one.label != two.label
                    or len(one.children) != len(two.children)):
                return False
            if one.label != 'cv':
                binders.update(c.variable for c in one.children
                               if c.variable is not None)
            return all(alike(a, b)
                       for a, b in zip(one.children, two.children,
                                       strict=True))

        return (alike(self.to_term(stated), self.to_term(claimed))
                and len(set(pairs.values())) == len(pairs)
                and all(mine == theirs or mine in binders
                        for mine, theirs in pairs.items()))

    def renamed(self, ex, depth):
        """An existential rewritten to bind variables nothing else holds."""
        whole, term, binding = self.to_term(ex), self.to_term(ex), {}
        for _ in range(depth):
            if term.label != 'wrex':
                break
            fresh = self.spare_var()
            binding[term.children[1].variable] = kernel.Term(
                variable=self.sigs[fresh].statement[1])
            term = term.children[0]
        return whole.substitute(binding).rpn(self.flabel)

    def carried(self, cite, facts, lines):
        """A cited line's proof, said where the citing step sits.

        A line proved before a block opened holds inside it too, and the
        scope carries a copy that says so. The line's own proof states it at
        the scope it was made in, which is not where a step inside the block
        can use it.
        """
        held = lines[cite]
        return facts.get(held.term, held.proof)

    def bound_in(self, term):
        """The variables an existential's own binders introduce.

        Outermost first, in the order the existential writes them, because a
        caller handing each of them a spare variable hands them out in this
        order and the proof it writes says which. A set here spelt the same
        proof two ways from one run to the next, and the build's report that
        nothing changed is the only evidence a change moved no proof.
        """
        out, rest = [], term
        while rest.label in ('wrex', 'wreu'):
            out.append(rest.children[1].variable)
            rest = rest.children[0]
        return tuple(out)

    def allowed(self, sig, binding, variables):
        """The innermost scope a lemma's disjointness conditions permit.

        `fsump1` forbids its summation variable in the antecedent, and the
        induction hypothesis is an equation between sums, so it holds that
        variable. The step is written inside that scope and cannot be proved
        there. It is proved one frame out and carried back in.

        What is left unbound is the scope, which a deduction-form lemma
        calls ph. A set variable left unbound is not: it is a letter the
        lemma binds inside itself, as `suprcl` binds the x and y of "S is
        bounded above", and it stands in the proof as its own name, which
        no scope mentions.
        """
        kinds = {v: t for t, v in sig.floats}
        forbidden = set()
        for a, b in sig.disjoint:
            for one, other in ((a, b), (b, a)):
                if kinds.get(other) == 'setvar':
                    continue
                if one in binding and other not in binding:
                    forbidden |= {self.flabel.get(n, n)
                                  for n in binding[one].names()}
        for index in range(len(self.frames) - 1, -1, -1):
            term = self.frames[index][0]
            if not forbidden & set(term.split()):
                return term, index
        return Declined('no scope satisfies the lemma'), None

    def frames_facts(self, frame, facts):
        """What is known at one frame, which is what was known when it opened."""
        return facts if frame == len(self.frames) - 1 else self.frames[frame][2]

    def carry(self, proof, claim, frame):
        """Bring a proof from an outer frame back to the innermost one."""
        for index in range(frame, len(self.frames) - 1):
            outer, added = self.frames[index][0], self.frames[index + 1][1]
            proof = self.seq(outer, claim, added, proof, 'adantr')
        return proof

    def with_cited(self, step, scope, known):
        """The facts a lemma is answered from, what the step cites first.

        Each line the step cites is taken apart on its own and laid over the
        scope's copies of the same claims. The scope holds one proof per
        claim, and which line put it there is not the step's to choose:
        `thm:stdlib/reasoning/from-contradiction` asks for P and not P, the
        step cites the line joining them, and the scope held each from the line before.
        """
        # First in order as well, because a lemma's open antecedent is
        # matched against these in turn and takes the first that fits:
        # `pm2.21` asks for a negation, and the one it wants is the one the
        # step cites, not the first the scope happens to hold.
        # A lemma whose disjointness conditions forbid the innermost scope is
        # proved in an outer one (`allowed`), and there a line proved further
        # in does not hold: its proof states it under the scope it was made
        # in, and handed to the lemma it is a proof of another statement,
        # which the verifier refuses. Only what that scope holds is offered.
        outer = bool(self.frames) and scope != self.frames[-1][0]
        cited = {}
        for ref in (step.just.refs if step is not None else ()):
            line = self.lines.get(ref)
            if line is None or (outer and line.term not in known):
                continue
            parts = {line.term: self.carried(ref, known, self.lines)}
            self.unpack(line.term, parts[line.term], scope, parts)
            cited.update(parts)
        return {**cited,
                **{k: v for k, v in known.items() if k not in cited}}

    def join(self, step, node, term, scope, facts, lines):
        """Two lines paired, which is one thing inside a contradiction and
        another outside it.

        Inside, it emits nothing: `pm2.65d` closes the block and consumes
        both joined lines itself, so the join only records which pair. Inside
        a case it is `jca`, and the lines are paired by what they claim, since
        the text lists them in the order they were derived and the conclusion
        states them in the theorem's order. `ELABORATION.md` requirement 8.
        """
        self.joined = [lines[ref].term for ref in step.just.refs]
        if self.enclosing is not None \
                and self.enclosing.owner.just.head == 'contradiction':
            return None
        wanted = self.claim_of(' '.join(step.claim))
        held = {lines[ref].term: self.carried(ref, facts, lines)
                for ref in step.just.refs}
        # One line joined is that line restated: a case whose assumption is
        # the block's claim ends on it, as the intermediate value proof's
        # second case does with `join C2`.
        if len(step.just.refs) == 1:
            if wanted not in held:
                raise self.defect(step.line,
                                  'the joined line is not what the step '
                                  'claims')
            return held[wanted]
        left, right = self.to_term(wanted).children
        pair = [left.rpn(self.flabel), right.rpn(self.flabel)]
        if not all(p in held for p in pair):
            raise self.defect(step.line,
                              'the joined lines are not what the step claims')
        return self.seq(scope, *pair, *(held[p] for p in pair), 'jca')
