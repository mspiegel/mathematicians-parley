"""The matcher: a lemma fitted to a claim.

This is the third of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given a lemma's statement, a claim, and the facts a
step names, it produces what the lemma's variables stand for and the
antecedents left to discharge, and discharges them. `settle` is the search
for a side condition the page does not write, through the lemmas
`rules.MEMBERSHIP` declares; `apply_lemma` fits one named lemma; `rewrite`
and `descend` carry an equation to where it is used inside a term.

What it matches modulo is written here as cases: a claim spelt with other
bound letters (`respelt`, `renaming`), a biconditional read either way
(`fits`, `one_direction`), an equation that says a term another way
(`rewritten`, `said_otherwise`), a lemma's implicit substitution
(`instanced`, `substituted_slot`, `as_class`), an existential introduced or
eliminated (`witnessed`, `introduced`, `through_existential`), and a
conjunct projected (`as_conjunct`).
"""
import kernel
import rules
from parse import Declined, declined
from rules import TURNED
from spell import Proof, seq

# The kinds of difference the one walk closes where a lemma's conclusion, or a
# fact, and what is wanted are both known and differ in places (`closing`).
# Each is a method `closed_<kind>`, and each closes its difference with proof
# steps:
#   held      an equation in hand says the two are equal
#   cited     the equation a step cites, which rewrote the place
#   assumed   the equation a lemma's own hypothesis assumes
#   standard  the two have one standard form (`same`, `rules.STANDARD`)
#   toward    a term carried to its standard form, which `standard` asks
DIFFERENCES = ('held', 'cited', 'assumed', 'standard', 'toward')


class Matcher:
    # --- facts the text never writes ----------------------------------------

    def settle(self, wanted, scope, facts, depth=3, step=None, lines=None):
        """A proof of something a step needs and the text does not write.

        `depth` bounds how many declared lemmas a chain applies one on top
        of another, and three is the deepest chain in the corpus: step 2.1
        of the geometric series needs `A^0 ∈ ℂ`, which is `recn` from
        `A^0 ∈ ℝ`, which is `reexpcl` asking `0 ∈ ℕ₀`, which is `0nn0`.
        Three other theorems need three as well. That a term is a set is not
        searched for and spends none of it (`made_a_set`), and neither does
        splitting a conjunction: there is one way to prove both halves, and
        the parts are smaller.

        What is offered is only what the proof being built may rest on
        (`resting_on`), so a route through a line the step does not name
        is not there to be found, whatever order the lemmas are tried in.

        A cited lemma asks side conditions of its own — that an index is in
        the upper integers, that a summand is complex — and those are not
        `requires` lines, because to a reader they are not steps. They are
        settled from the lemmas `rules.MEMBERSHIP` names, by matching what
        each concludes against what is wanted, and failing that from what is
        wanted read through an equation the step cites (`rewritten`).

        A step is passed only where one is there to have cited a witness,
        which is what lets an existential be proved at all. Side conditions
        pass none, so they stay what they are: settled from declared
        lemmas, never by finding a fact that happens to fit.
        """
        if self.resting is not None:
            facts = {k: v for k, v in facts.items()
                     if getattr(v, 'origin', frozenset()) <= self.resting}
        rpn = wanted.rpn(self.flabel)
        if rpn in facts:
            return facts[rpn]
        # A number's membership of a number system is worked out from the
        # numeral, not searched for, and spends none of the depth: a digit
        # is set.mm's label for it, `9cn` or `9nn0`, and 10 or 10^0 − 1 is
        # built from its digits (`numeral_within`). Spending depth on it
        # left 10^k ∈ ℤ, deep inside a sum's term, one level short of 10.
        if wanted.label == 'wcel' and len(wanted.children) == 2 \
                and wanted.children[1].label in rules.SYSTEMS \
                and not set(wanted.children[0].rpn(self.flabel).split()) \
                - rules.NUMERIC:
            # Inside the search that works out one number, the numbers it
            # is built from are looked up and not searched for again: each
            # starting its own search made 21,000 of them for one theorem.
            number = (self.digit_within(wanted, scope, facts)
                      if self.numbering
                      else self.numeral_within(wanted, scope, facts))
            if not declined(number):
                return number
        # Whether a term is a set is read off its structure, not searched
        # for: the constructor at its head says which lemma, and what the
        # lemma asks is its parts' sethood, which comes back here.
        if (wanted.label == 'wcel' and len(wanted.children) == 2
                and wanted.children[1].rpn(self.flabel) == 'cvv'):
            made = self.made_a_set(wanted, scope, facts)
            if not declined(made):
                return made
        # A membership a requires line wrote in another number system is the
        # one to carry, before the lemmas below are tried in their order:
        # `nncn` stands before `recn`, and would take `A ∈ ℂ` from the
        # hypothesis `A ∈ ℕ` rather than from the line saying `A ∈ ℝ`.
        if wanted.label == 'wcel' and len(wanted.children) == 2:
            found = self.bridged(wanted.children[0].rpn(self.flabel),
                                 wanted.children[1].rpn(self.flabel),
                                 scope, facts)
            if found is not None:
                return found
        # A sum, difference, product, power or negation is in a number
        # system because its parts are, and that is read off the operation,
        # spending none of the depth (`closed_under`).
        if wanted.label == 'wcel' and len(wanted.children) == 2 \
                and wanted.children[1].label in rules.SYSTEMS:
            made = self.closed_under(wanted, scope, facts, depth)
            if not declined(made):
                return made
        if wanted.label in rules.BOUND:
            # A `define` and a `fix` may write the same letter, and one of
            # them is renamed so that they do not collide. The line is then
            # the line wanted spelt with another binder, which is the same
            # line: `ralrnmpt` asks over the name its map binds where the
            # proof wrote its own.
            for said, proof in facts.items():
                spelt = self.respelt(proof, said, rpn, scope)
                if spelt is not None:
                    return spelt
        if depth > 0:
            joined = self.conjoined(
                wanted, scope,
                lambda one: self.settle(one, scope, facts, depth, step,
                                        lines))
            if joined is not None:
                return joined
            if wanted.label == 'wrex' and step is not None:
                return self.witnessed(step, wanted, scope, facts,
                                      lines or {})
            if wanted.label == 'wral':
                # A side condition may be asked of every member at once:
                # `ralrnmpt` wants each of its map's values to be a set. The
                # name is fixed, the condition settled of it, and
                # `ralrimiva` gives it back, which is `as_generalised` over
                # a declared lemma rather than over a cited one.
                #
                # Going under the binder spends no depth, as splitting a
                # conjunction spends none. It is one claim said of one
                # member, not a step of the chain the bound is there to cut
                # off, and spending it stopped `f1mpt` halfway.
                body, variable, over = wanted.children
                member = self.seq(f'{variable.rpn(self.flabel)} cv',
                             over.rpn(self.flabel), 'wcel')
                with self.frames_kept():
                    inner, lifted = self.widen(scope, facts, member)
                    made = self.settle(body, inner, lifted, depth)
                if declined(made):
                    return made
                return self.seq(scope, body.rpn(self.flabel),
                           variable.rpn(self.flabel),
                           over.rpn(self.flabel), made, 'ralrimiva')
            # Every lemma is tried as it is written before any is read
            # backwards, so that a biconditional turned round never stands
            # in for one that says what is wanted outright.
            for backwards in (False, True):
                for label in self.declared(wanted, backwards):
                    found = self.fits(label, self.sigs[label], wanted, scope,
                                      facts, depth, backwards)
                    if found is not None:
                        return found
            found = self.said_otherwise(wanted, scope, facts, depth)
            if found is not None:
                return found
            found = self.rewritten(wanted, scope, facts, depth)
            if not declined(found):
                return found
        return self.no('cannot settle {}', rpn)

    def declared(self, wanted, backwards):
        """The declared lemmas that could conclude what is wanted, in order.

        `rules.MEMBERSHIP` is the one place a lemma is declared, and this
        reads it through an index built from each lemma's own statement:
        the constructor each reading of it can end on (`fits` and `fitting`
        read a lemma the same way), and, for a membership, the class where
        the lemma fixes one. A lemma the index leaves out is one whose
        conclusion cannot match what is wanted at any reading, so nothing
        is lost that `fits` would have found; what the index saves is
        asking each of them. Nothing is kept by hand, so a lemma declared
        for a new proof is found the day it is declared.
        """
        keys = self.head_keys(wanted)
        return [label for label, (heads, _role) in self.lemma_index().items()
                if heads[backwards] & keys]

    def declared_as(self, role):
        """The declared lemmas of one role, in the order they are declared.

        A lemma's role is read off its statement (`role`): an `equation`
        that `said_otherwise` rewrites by, an `equivalence` that `crossed`
        reads as one claim said two ways, a `carrier` that `bridged` takes
        from one number system to another, and otherwise a `side`
        condition. `settle` tries every role.
        """
        return [label for label, (_heads, said) in self.lemma_index().items()
                if said == role]

    def lemma_index(self):
        """Every declared lemma set.mm has, with its readings and its role."""
        if self.lemma_heads is None:
            self.lemma_heads = {}
            for label in rules.MEMBERSHIP:
                sig = self.sigs.get(label)
                if sig is not None:
                    self.lemma_heads[label] = (self.heads(sig),
                                               self.role(sig))
        return self.lemma_heads

    def role(self, sig):
        """What a declared lemma is for, read off what it states."""
        whole = self.syntax.statement(sig)
        if sig.essentials:
            return 'side'
        ends = whole
        while ends.label == 'wi':
            ends = ends.children[1]
        if ends.label == 'wceq' and len(ends.children) == 2:
            return 'equation'
        if ends.label == 'wb':
            return 'equivalence'
        if len(sig.floats) == 1 and whole.label == 'wi':
            given, gives = whole.children
            if given.label == 'wcel' and gives.label == 'wcel' \
                    and given.children[0].variable is not None \
                    and given.children[0].rpn(self.flabel) \
                    == gives.children[0].rpn(self.flabel):
                return 'carrier'
        return 'side'

    def heads(self, sig):
        """What each reading of a lemma can end on, forwards and backwards.

        The readings are the ones `fits` makes: the statement whole, and a
        biconditional's far side forwards or its near side backwards, after
        what it asks; `fitting` then peels implications, and may stop at
        any of them.
        """
        whole = self.syntax.statement(sig)
        reads = whole
        while reads.label == 'wi':
            reads = reads.children[1]
        said = whole if whole.label == 'wb' else reads
        forward, backward = [whole], []
        if said.label == 'wb':
            forward.append(said.children[1])
            backward.append(said.children[0])

        def ends(starts):
            out = set()
            for node in starts:
                out.add(self.head_key(node))
                while node.label == 'wi' and node.variable is None:
                    node = node.children[1]
                    out.add(self.head_key(node))
            return out
        return {False: ends(forward), True: ends(backward)}

    def head_key(self, node):
        """How a lemma's conclusion constrains what it can match.

        Any claim where it is a variable, a membership of one class where it
        names a closed one, and otherwise its constructor.
        """
        if node.variable is not None:
            return 'any'
        if node.label == 'wcel' and len(node.children) == 2 \
                and not node.children[1].names():
            return ('wcel', node.children[1].rpn(self.flabel))
        return (node.label, None)

    def head_keys(self, wanted):
        """The keys a lemma's conclusion may carry and still match `wanted`."""
        if wanted.variable is not None:
            return {'any'}
        keys = {'any', (wanted.label, None)}
        if wanted.label == 'wcel' and len(wanted.children) == 2:
            keys.add(('wcel', wanted.children[1].rpn(self.flabel)))
        return keys

    def rewritten(self, wanted, scope, facts, depth):
        """What is wanted, with a term in it put as an equation in hand says.

        `hashgt0elex` asks that a set's size be positive, and the subsets
        proof says what the size is: |X| = k + 1, the line the step cites.
        Nothing declared says a size is positive, and something does say
        k + 1 is, once the size is read as the line says. So the term is
        replaced by what the equation equates it to, what is left is
        settled, and the congruence carries it back.

        The equations are the ones in `facts`, which during a step is what
        the step names and the sorts (`resting_on`), and the sorts are
        never equations. So this rewrites only by a line the step cites,
        and a line merely in scope rewrites nothing.

        Only a term built from others is replaced, never a name or a
        constant. Putting a name's value in its place is what a
        `substitute` line writes, so a reader sees it done; a size or a sum
        read as a line equates it is the step's own business. No proof in
        the corpus needs more, and none changes when names are allowed too.
        Each rewrite spends a level, and a term already being rewritten is
        not rewritten again, so the rewrites stop.
        """
        want = wanted.rpn(self.flabel)
        if want in self.rewriting:
            return self.no('{} is already being rewritten', want)
        self.rewriting.add(want)
        try:
            return self.rewrite_by_facts(wanted, want, scope, facts, depth)
        finally:
            self.rewriting.discard(want)

    def rewrite_by_facts(self, wanted, want, scope, facts, depth):
        """One pass over the equations in hand, for `rewritten`."""
        for said in list(facts):
            equation = self.to_term(said)
            if equation.label != 'wceq' or len(equation.children) != 2:
                continue
            left, right = equation.children
            for old, new in ((left, right), (right, left)):
                if old.variable is not None or not old.children \
                        or old.label == 'cv':
                    continue
                was, now = old.rpn(self.flabel), new.rpn(self.flabel)
                # A numeral is a constant however set.mm spells it — 10 is
                # the decimal `; 1 0` — and so is a sum of them. A cited
                # 9 + 1 = 10 rewrote each into the other at every level of
                # every search that failed, and a build ran for minutes.
                if not set(was.split()) - rules.NUMERIC:
                    continue
                put = self.replaced(wanted, was, new)
                if put.rpn(self.flabel) == want:
                    continue
                under = self.settle(put, scope, facts, depth - 1)
                if declined(under):
                    continue
                alike = self.congruence(
                    put, wanted, scope, facts, None,
                    self.closing(('cited', was, now, said, old is left)))
                if declined(alike):
                    continue
                return self.seq(scope, put.rpn(self.flabel), want, under,
                                alike, 'mpbid')
        return self.no('no equation in hand rewrites {}', want)

    def replaced(self, term, was, new):
        """`term` with every occurrence of the term spelt `was` put as `new`."""
        if term.rpn(self.flabel) == was:
            return new
        if term.variable is not None or not term.children:
            return term
        return kernel.Term(term.label,
                           tuple(self.replaced(c, was, new)
                                 for c in term.children))

    def said_otherwise(self, wanted, scope, facts, depth):
        """What is wanted, held by the scope under another name for a term.

        `divalg` bounds the remainder by the absolute value of the divisor
        and the readable line bounds it by the divisor, which are the same
        bound because the divisor is a natural number. So a declared
        equation is asked whether the fact in hand is the fact wanted said
        differently, and the congruence carries it across.

        The equation is declared, like everything else this may lean on,
        and it is asked only of terms the wanted actually contains — a
        lemma that rewrote anywhere would reach claims by means the text
        never names.

        A term already being asked about is not asked about again. What
        this reaches through eventually asks `settle` afresh, which starts
        its depth over, so the two of them together have nothing that must
        decrease and would go round until the stack gave out. It used to go
        round until the stack gave out and then catch that, which is a
        stack overflow read as a route declining; this is the same cut made
        where it can be seen. `supplying` guards `requires` the same way.
        """
        want = wanted.rpn(self.flabel)
        if want in self.saying:
            return None
        self.saying.add(want)
        try:
            return self.otherwise(wanted, want, scope, facts, depth)
        finally:
            self.saying.discard(want)

    def otherwise(self, wanted, want, scope, facts, depth):
        """One pass over the facts in hand, for `said_otherwise`.

        The first whose standard form is what is wanted's (`same`), which
        is where a declared equation such as `exp0` stands between them.
        """
        for said, proof in list(facts.items()):
            if said == want:
                continue
            alike = self.same(self.to_term(said), wanted, scope, facts)
            if not declined(alike):
                return self.seq(scope, said, want, proof, alike, 'mpbid')
        return None

    def fits(self, label, sig, wanted, scope, facts, depth, backwards):
        """Whether one lemma settles what is wanted, and how.

        A biconditional says two things, so it can be read either way:
        `elnnuz` puts a natural number in the upper integers from its left
        side, and `eluz2` puts something there from an inequality, which is
        its right. Which way is the caller's, since reading one backwards
        is a last resort.

        A lemma may ask something and only then say its two things: `rexss`
        wants one set inside another before it will say that quantifying
        over the smaller is quantifying over the larger with the smaller in
        the body. So the asking is peeled off first and what is left is read
        the same way a bare biconditional is.
        """
        whole = self.syntax.statement(sig)
        asks, joins, reads = [], [], whole
        while reads.label == 'wi':
            asks.append(reads.children[0])
            joins.append('wi')
            reads = reads.children[1]
        if whole.label == 'wb':
            side = 0 if backwards else 1
            readings = [([whole.children[1 - side]], ['wb'],
                         whole.children[side])]
            # and the biconditional itself, which is what `crossed` asks
            # for when `rextru` is the bridge between two existentials
            if not backwards:
                readings.append(((), (), whole))
        elif reads.label == 'wb':
            # Asked something and then said two things. Either side may be
            # what is wanted, and so may the whole biconditional, which is
            # what a caller wanting the equivalence itself asks for.
            side = 0 if backwards else 1
            readings = [([*asks, reads.children[1 - side]], [*joins, 'wb'],
                         reads.children[side])]
            if not backwards:
                readings.append(((), (), whole))
        else:
            # Nothing was said two ways, so the statement is read as it
            # stands and `fitting` peels it.
            readings = [] if backwards else [((), (), whole)]
        for antecedents, held, side in readings:
            found = self.fitting(label, sig, whole, list(antecedents),
                                 list(held), side, wanted, scope, facts,
                                 depth, backwards)
            if found is not None:
                return found
        return None

    def fitting(self, label, sig, whole, antecedents, joins, reads,
                wanted, scope, facts, depth, backwards=False):
        """One reading of a lemma, applied to what is wanted.

        A lemma may ask more than one thing before it says anything —
        `ltle` wants both sides real and then the strict relation — so its
        antecedents are peeled until what is left is what is wanted.

        `joins` says how each was joined to what followed it, which is what
        decides the lemma that discharges it. A reading that crosses a
        biconditional has one of each and they do not discharge alike.
        """
        variables = whole.names()
        binding = None
        while True:
            binding = kernel.match(reads, wanted, {}, variables)
            if binding is not None:
                break
            if reads.label != 'wi':
                return None
            antecedents.append(reads.children[0])
            joins.append('wi')
            reads = reads.children[1]

        # What the lemma concludes need not fix everything it asks, so an
        # antecedent still open is matched against something already known,
        # whole, and failing that a conjunct at a time, as `apply_lemma`
        # does: `ffvelcdm` asks `F : A --> B` and `C e. A` together, and
        # only the line saying what F maps between says what A is. What a
        # naming hypothesis decides comes first, as in `apply_lemma`:
        # `f1mpt` names its map, and a conjunct of what it asks matched
        # against a line otherwise binds the map's body to that line's.
        binding = self.opened(antecedents,
                              self.read_off(sig, binding, variables), facts,
                              variables)
        return self.fitted(label, sig, antecedents, joins, wanted, scope,
                           facts, depth, backwards, binding)

    def opened(self, antecedents, binding, facts, variables):
        """The binding with what the antecedents leave open filled in.

        A conjunct asking where to look for something rather than anything
        of it is left to `sethood`, which reads it so, and is not matched:
        `f1mpt` asks its map's values to lie in B, and matched alone against
        a fact putting one of them in some set, it bound B to that set and
        `add-element-bijection` failed.

        Every antecedent is matched whole before any is taken apart, so a
        conjunct matched alone never decides what a later antecedent says
        outright: `hashvnfin` asks `N e. NN0` beside `S e. V` and then
        `( # ` S ) = N`, and the first line in ℕ₀ is not the size.
        """
        binding = dict(binding)
        whole = []
        for slot in antecedents:
            if not slot.names() - set(binding):
                continue
            for held in facts:
                filled = kernel.match(slot, self.to_term(held), dict(binding),
                                      variables)
                if filled is not None:
                    binding = filled
                    break
            else:
                whole.append(slot)
        for slot in whole:
            for piece in self.conjuncts_of(slot):
                if not piece.names() - set(binding) \
                        or self.sethood(piece, binding):
                    continue
                for held in facts:
                    filled = kernel.match(piece, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            # A class neither the claim nor a fact fixes is set.mm asking
            # where to look for the thing rather than asking anything of it,
            # which `apply_lemma` reads the same way: `pwexg` wants a class
            # holding the set whose power class is about to be one, and _V
            # holds every set. What is left is then settled.
            for open_slot in self.sethood(slot, binding):
                binding[open_slot] = kernel.Term('cvv')
        return binding

    def fitted(self, label, sig, antecedents, joins, wanted, scope, facts,
               depth, backwards, binding):
        """The lemma proved under one binding, or None where it is not."""
        variables = self.syntax.statement(sig).names()
        # A declared lemma may state a hypothesis in full rather than ask for
        # it, which is a spelling and not a difference in what it leans on:
        # `f1mpt` names its map that way. The two kinds it states are the two
        # `prove_essential` already knows — a naming and a relating — and
        # they are also what says which variables the claim did not fix.
        binding = self.instanced(sig, self.read_off(sig, binding, variables))
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding),
            scope, facts) for e in sig.essentials]
        if any(declined(one) for one in essentials):
            return None
        proof = self.ap(label, self.spelt(binding), *essentials)
        if not antecedents:
            return self.seq(wanted.rpn(self.flabel), scope, proof, 'a1i')
        for i, slot in enumerate(antecedents):
            asks = slot.substitute(binding)
            rest = wanted.rpn(self.flabel)
            for later, join in reversed(list(zip(antecedents[i + 1:],
                                                 joins[i + 1:],
                                                 strict=True))):
                said = later.substitute(binding).rpn(self.flabel)
                # A biconditional read backwards states its sides the
                # other way round from the order they are taken in.
                rest = (self.seq(rest, said, 'wb')
                        if join == 'wb' and backwards
                        else self.seq(said, rest, join))
            under = self.settle(asks, scope, facts, depth - 1)
            if declined(under):
                return None
            first = proof.text.rsplit(None, 1)[-1] == label
            fold = rules.DISCHARGE[(joins[i], first)]
            if joins[i] == 'wb' and backwards:
                fold = 'sylibr' if first else 'mpbird'
            proof = self.seq(scope, asks.rpn(self.flabel), rest, under, proof,
                        fold)
        return proof

    # --- congruence ---------------------------------------------------------

    def shape(self, pattern):
        """A target read as a tree, so a rewrite can walk down it.

        A target need not be one constructor. `S(_)` is a sum over a range
        that holds the hole, so reaching the hole passes a `csu` and then a
        `co`, and each level wants its own congruence lemma.
        """
        if pattern in self.shapes:
            return self.shapes[pattern]
        stack = []
        for token in pattern.split():
            if token.startswith('_'):
                stack.append(('hole', int(token[1:]) - 1))
                continue
            count = len(self.sigs[token].floats)
            if not count:
                stack.append(('const', token))
                continue
            args = stack[len(stack) - count:]
            del stack[len(stack) - count:]
            # The operation is an operand of the lemma that rewrites under
            # it where it is a constant, as `cabs` is in |x|. Where it is a
            # hole it is an argument like any other: `application` targets
            # `_2 _1 cfv` and its function is `f`, which taken for a label
            # was its hole's index, and a zero `seq` leaves out.
            if token in rules.WRAPS and args[-1][0] == 'const':
                stack.append(('app', args[-1][1], token, args[:-1]))
            else:
                stack.append(('app', token, None, args))
        self.shapes[pattern] = stack[0]
        return stack[0]

    @staticmethod
    def holds(tree, wanted):
        if tree[0] == 'hole':
            return tree[1] == wanted
        if tree[0] == 'const':
            return False
        return any(Matcher.holds(k, wanted) for k in tree[3])

    def spell(self, tree, holes):
        if tree[0] == 'hole':
            return holes[tree[1]]
        if tree[0] == 'const':
            return tree[1]
        _k, label, wrap, kids = tree
        parts = [self.spell(k, holes) for k in kids]
        return self.seq(*parts, label, wrap) if wrap else self.seq(*parts, label)

    def rewrite(self, node, old, new, scope, eqproof):
        """A proof that `node` equals `node` with `old` replaced by `new`.

        The path from the root of the claim to the occurrence decides the
        lemmas, one per step along it, and which hole the occurrence sits in
        decides which lemma. Nothing is searched for.
        """
        if self.term(node) == old:
            return new, eqproof
        # A binder's variable fills its slot as itself, and nothing rewrites
        # it: the claim is about what the binder ranges over, not about the
        # name it ranges under.
        bound = self.binders.get(node.notation, ())
        # The body speaks of what the binder introduces, as in `term`: the
        # lower limit of a sum is rewritten beside a summand that names k.
        with self.names_kept():
            for i in bound:
                said = node.children[i].text
                self.names[said] = f'{self.binder_var(said)} cv'
            holes = [self.binder_var(c.text) if i in bound else self.term(c)
                     for i, c in enumerate(node.children)]
            after, proofs = list(holes), {}
            for i, child in enumerate(node.children):
                if i in bound or old not in self.term(child):
                    continue
                made = self.rewrite(child, old, new, scope, eqproof)
                if declined(made):
                    return made
                after[i], proofs[i] = made
        if not proofs:
            return Declined(f'nothing to rewrite in {self.term(node)}')
        return self.descend(self.shape(self.spelling(node)), holes, after,
                            proofs, scope)

    def descend(self, tree, before, after, proofs, scope):
        """Walk a target down to the holes that changed, a lemma a level."""
        if tree[0] == 'hole':
            return after[tree[1]], proofs[tree[1]]
        if tree[0] == 'const':
            return Declined('no hole changed under this target')
        _k, label, wrap, kids = tree
        was = [self.spell(k, before) for k in kids]
        now, deeper, slots = list(was), [], []
        for slot, kid in enumerate(kids):
            if not any(self.holds(kid, h) for h in proofs):
                continue
            made = self.descend(kid, before, after, proofs, scope)
            if declined(made):
                return made
            now[slot], under = made
            deeper.append(under)
            slots.append(slot)
        if not slots:
            return Declined('no hole changed under this target')
        # An operation or a relation is itself an operand of the lemma that
        # rewrites under it; a constructor that takes its arguments directly
        # is not. What changed comes first, old beside new, then the rest.
        built = self.seq(*now, label, wrap) if wrap else self.seq(*now, label)
        if (wrap or label) == 'csu' and 1 in slots:
            made = self.summand_changed(scope, was, now,
                                        dict(zip(slots, deeper, strict=True)))
            return made if declined(made) else (built, made)
        moved = [x for slot in slots for x in (was[slot], now[slot])]
        rest = [o for j, o in enumerate(was) if j not in slots]
        return built, self.seq(scope, *moved, *rest, label if wrap else '',
                          *deeper, rules.CONGRUENCE[(wrap or label,
                                                    tuple(slots))])

    def summand_changed(self, scope, was, now, proofs):
        """A sum rewritten where its summand changes, and its range maybe.

        The claim of an induction over a sum holds the variable in the
        summand as well as the limit: the binomial theorem's n is in both.
        `sumeq2sdv` rewrites the summand from an equation with no index in
        it, which set.mm lets it do only where the scope does not mention
        the index, as the induction's `x = y` does not. The range, where it
        changes too, is rewritten first by `sumeq1d`, and `eqtrd` joins the
        two. A scope that mentions the index declines here: set.mm's own
        lemma would be refused by the verifier.
        """
        limits, summand, index = was
        if index in scope.split():
            return Declined('the scope mentions the index the sum binds')
        rewritten = self.ap('sumeq2sdv', {'ph': scope, 'A': now[0],
                                          'B': summand, 'C': now[1],
                                          'k': index}, proofs[1])
        if 0 not in proofs:
            return rewritten
        moved = self.ap('sumeq1d', {'ph': scope, 'A': limits, 'B': now[0],
                                    'C': summand, 'k': index}, proofs[0])
        return self.ap('eqtrd', {'ph': scope,
                                 'A': self.seq(limits, summand, index, 'csu'),
                                 'B': self.seq(now[0], summand, index, 'csu'),
                                 'C': self.seq(now[0], now[1], index, 'csu')},
                       moved, rewritten)

    # --- closing a difference -----------------------------------------------

    def closing(self, *rows):
        """What the walk asks where two terms differ, row by row.

        `congruence` walks two terms together and asks this at every place
        they differ, outermost first; the first row that closes the
        difference gives the proof there, and where none does the walk goes
        a level in. Each row is one kind in `DIFFERENCES`, with what that
        kind needs to know, and each closes a difference with a proof step.
        """
        def leaf(one, other, where, held):
            for kind, *given in rows:
                found = getattr(self, f'closed_{kind}')(one, other, where,
                                                        held, *given)
                if found is not None:
                    return found
            return None
        return leaf

    def closed_held(self, one, other, where, held):
        """Two terms an equation in hand says are equal."""
        if one.rpn(self.flabel) == other.rpn(self.flabel):
            return None
        asked = self.seq(one.rpn(self.flabel), other.rpn(self.flabel), 'wceq')
        if asked not in held:
            return None      # the walk goes on to where they differ
        return held[asked]

    def closed_cited(self, one, other, where, held, was, now, said, flip):
        """The place one cited equation rewrote, carried back.

        The line says `was = now` or `now = was` (`flip`), and what carries
        the settled term back is `now = was`.
        """
        if (one.rpn(self.flabel) != now
                or other.rpn(self.flabel) != was):
            return None
        if said not in held:
            return self.no('{} is not in hand here', said)
        return (self.seq(where, was, now, held[said], 'eqcomd')
                if flip else held[said])

    def closed_assumed(self, one, other, where, held, was, now, under):
        """The place a lemma's own assumed equation says the two agree.

        The equation is handed over as a fact rather than reproved at the
        leaf: the walk widens the scope where it passes a binder, and a
        proof under the scope it started at would not be a proof under that
        one.
        """
        return (held.get(under)
                if one.rpn(self.flabel) == was
                and other.rpn(self.flabel) == now else None)

    # --- one standard form -------------------------------------------------

    def same(self, given, want, scope, facts, step=None):
        """( scope -> given <-> want ), or `=` for classes, where the two have
        one standard form; a decline where they do not.

        What a lemma says and what the page says may differ in how they are
        written and not in what they say: `k · 2` and `2 · k`, a three-way
        "or" and two nested ones, ℝ⁺ and ℝ with a positive bound, a letter
        bound by another name. Each is a rule of `rules.STANDARD` or
        `rules.SYMMETRIC`, or a renaming, and the two are the same claim
        exactly when their standard forms agree up to the letters they
        bind. The walk proves it at the smallest places they differ.
        """
        kept = self.binding
        self.binding = self.letters_bound(given) | self.letters_bound(want)
        try:
            return self.congruence(given, want, scope, facts, step,
                                   self.closing(('standard',)))
        finally:
            self.binding = kept

    @staticmethod
    def letters_bound(term):
        """The variables a term binds.

        Each one standing directly under a constructor other than `cv`, as
        `rebound` reads them.
        """
        out, rest = set(), [term]
        while rest:
            node = rest.pop()
            if node.variable is not None:
                continue
            if node.label != 'cv':
                out.update(c.variable for c in node.children
                           if c.variable is not None)
            rest.extend(node.children)
        return frozenset(out)

    def order_key(self, term):
        """What decides which of a symmetric pair goes first.

        The term as reverse Polish, with every letter the statement binds
        read as a blank: which letter a binder uses is no part of what a
        statement says, so it cannot decide an order, or one claim bound
        with `i` and `j` and the same claim bound with `m` and `y` would
        come out in two orders.
        """
        if term.variable is not None:
            return '_' if term.variable in self.binding \
                else self.flabel[term.variable]
        return ' '.join([*(self.order_key(c) for c in term.children),
                         term.label])

    def standard(self, term):
        """The term with every rule applied, parts first, each pair in order.

        What a rule asks — `rexss` a subset, `exp0` a complex number — is
        not asked here: this says what the term comes to, and the proof
        that it does asks it where the rule is applied.
        """
        key = (term.rpn(self.flabel), self.binding)
        found = self.standards.get(key)
        if found is not None:
            return found
        if term.variable is not None or not term.children:
            found = term
        else:
            parts = kernel.Term(term.label,
                                tuple(self.standard(c) for c in term.children))
            step = self.standard_step(parts)
            found = parts if step is None else self.standard(step[1])
        self.standards[key] = found
        return found

    def standard_step(self, term):
        """One rewrite toward the standard form at the head of `term`.

        `(how, what it becomes)`: a rule of `rules.STANDARD` by its label, or
        `eqcom` or `commuted` for a symmetric pair put in order — the side
        whose `order_key` sorts first on the left, and a tie left as it
        stands. None where nothing rewrites the head.
        """
        if term.variable is not None:
            return None
        for label, given, gives, names in self.rewrites(conditional=False):
            bound = kernel.match(given, term, {}, names)
            if bound is not None and not gives.names() - set(bound):
                return label, gives.substitute(bound)
        if term.label == 'wceq' and len(term.children) == 2:
            a, b = term.children
            if self.order_key(b) < self.order_key(a):
                return 'eqcom', kernel.Term('wceq', (b, a))
        for label, (i, j), fixed in self.commutes:
            if term.label != label or len(term.children) != len(fixed) + 2:
                continue
            if any(term.children[k].rpn(self.flabel) != token
                   for k, token in fixed.items()):
                continue
            if self.order_key(term.children[j]) \
                    < self.order_key(term.children[i]):
                kids = list(term.children)
                kids[i], kids[j] = kids[j], kids[i]
                return 'commuted', kernel.Term(label, tuple(kids))
        return None

    def rewrites(self, conditional):
        """The rules of `rules.STANDARD` set.mm has, as (label, the side
        rewritten, the side it becomes, the lemma's variables).

        A rule that asks something first — `exp0` a complex number,
        `nn0absid` a whole number, `rexss` a subset — holds only where that
        is so, which a standard form, worked out before anything is proved,
        cannot know: |x| is x only for a whole number. Such a rule is
        `conditional`, and is used only where it closes a difference the
        walk has found, with what it asks settled there (`closed_standard`).
        """
        out = []
        for label, side in rules.STANDARD.items():
            sig = self.sigs.get(label)
            if sig is None:
                continue
            says = self.syntax.statement(sig)
            if (says.label == 'wi') != conditional:
                continue
            body = says
            while body.label == 'wi':
                body = body.children[1]
            out.append((label, body.children[1 - side], body.children[side],
                        says.names()))
        return out

    def standard_proof(self, cur, how, nxt, where, held):
        """( where -> cur <-> nxt ), or `=`, for one rewrite at the head.

        A rule's lemma is applied as `apply_lemma` applies any lemma, which
        settles what it asks from what is in hand; a commuting pair is the
        equation `settle` answers from the declared `addcom` and `mulcom`.
        """
        a, b = cur.rpn(self.flabel), nxt.rpn(self.flabel)
        if how == 'eqcom':
            left, right = (c.rpn(self.flabel) for c in cur.children)
            return self.seq(self.seq(a, b, 'wb'), where,
                            self.ap('eqcom', {'A': left, 'B': right}), 'a1i')
        if how == 'commuted':
            return self.settle(self.to_term(self.seq(a, b, 'wceq')), where,
                               held)
        wff = self.is_wff(cur)
        join = 'wb' if wff else 'wceq'
        if rules.STANDARD[how] == rules.RIGHT:
            return self.apply_lemma(how, self.to_term(self.seq(a, b, join)),
                                    where, held, None, crossing=False)
        made = self.apply_lemma(how, self.to_term(self.seq(b, a, join)),
                                where, held, None, crossing=False)
        if declined(made):
            return made
        if wff:
            return self.ap('bicomd', {'ph': where, 'ps': b, 'ch': a}, made)
        return self.ap('eqcomd', {'ph': where, 'A': b, 'B': a}, made)

    def is_wff(self, term):
        """Whether a term is a statement rather than a class."""
        label = term.label if term.variable is None \
            else self.flabel[term.variable]
        return self.sigs[label].statement[0] == 'wff'

    def chained(self, where, links):
        """One proof of the first term against the last.

        From `(x, y, proof)` links each proving `x` against `y`, joined by
        `bitrd` or `eqtrd`.
        """
        first, last, proof = links[0]
        wff = self.is_wff(first)
        start = first.rpn(self.flabel)
        for _was, now, more in links[1:]:
            mid, end = last.rpn(self.flabel), now.rpn(self.flabel)
            proof = (self.ap('bitrd', {'ph': where, 'ps': start, 'ch': mid,
                                       'th': end}, proof, more)
                     if wff else
                     self.ap('eqtrd', {'ph': where, 'A': start, 'B': mid,
                                       'C': end}, proof, more))
            last = now
        return proof

    def lifts(self, one, other):
        """Whether the walk can go a level in from these two.

        The same constructor, and a lemma in `rules.CONGRUENCE` for the
        places that differ; under an existential only its body may.
        """
        if one.variable is not None or other.variable is not None \
                or one.label != other.label \
                or len(one.children) != len(other.children):
            return False
        spelt = [c.rpn(self.flabel) for c in one.children]
        other_spelt = [c.rpn(self.flabel) for c in other.children]
        if one.label == 'wrex':
            return spelt[1:] == other_spelt[1:]
        places = range(len(spelt))
        if one.label in rules.WRAPS:
            if spelt[-1] != other_spelt[-1]:
                return False
            places = range(len(spelt) - 1)
        slots = tuple(i for i in places if spelt[i] != other_spelt[i])
        return not slots or (one.label, slots) in rules.CONGRUENCE

    def closed_toward(self, one, other, where, held):
        """`one` carried to `other`, its standard form.

        Where only the parts rewrite, the walk goes a level in; otherwise
        the parts are put in standard form first, the head is rewritten
        once, and what that gives is carried on the same way.
        """
        if one.rpn(self.flabel) == other.rpn(self.flabel):
            return None
        parts = kernel.Term(one.label,
                            tuple(self.standard(c) for c in one.children))
        if parts.rpn(self.flabel) == other.rpn(self.flabel) \
                and self.lifts(one, parts):
            return None
        links, cur = [], one
        if parts.rpn(self.flabel) != one.rpn(self.flabel):
            if not self.lifts(one, parts):
                return Declined('the parts cannot be rewritten in place')
            made = self.congruence(one, parts, where, held, None,
                                   self.closing(('toward',)))
            if declined(made):
                return made
            links.append((one, parts, made))
            cur = parts
        step = self.standard_step(cur)
        if step is None:
            return Declined('no rule rewrites the head')
        how, nxt = step
        made = self.standard_proof(cur, how, nxt, where, held)
        if declined(made):
            return made
        links.append((cur, nxt, made))
        if nxt.rpn(self.flabel) != other.rpn(self.flabel):
            made = self.congruence(nxt, other, where, held, None,
                                   self.closing(('toward',)))
            if declined(made):
                return made
            links.append((nxt, other, made))
        return self.chained(where, links)

    def closed_standard(self, one, other, where, held):
        """Two terms with one standard form, at the smallest place they
        differ: each carried to its standard form, and the two forms joined
        by a renaming where they differ only in the letters they bind.
        """
        if one.rpn(self.flabel) == other.rpn(self.flabel):
            return None
        # Two that differ only in the letters they bind are one claim by a
        # renaming, which is closed and asks nothing of the scope.
        if self.is_wff(one) and self.rebound(one.rpn(self.flabel),
                                             other.rpn(self.flabel)):
            renamed = self.renamed_apart(one, other)
            if renamed is not None:
                return self.seq(self.seq(one.rpn(self.flabel),
                                         other.rpn(self.flabel), 'wb'),
                                where, renamed, 'a1i')
        ours, theirs = self.standard(one), self.standard(other)
        said, want = ours.rpn(self.flabel), theirs.rpn(self.flabel)
        if said != want and not self.rebound(said, want):
            return self.conditioned(one, other, where, held)
        if self.lifts(one, other) and all(
                self.standard(a).rpn(self.flabel)
                == self.standard(b).rpn(self.flabel)
                for a, b in zip(one.children, other.children, strict=True)):
            return None                       # the walk goes a level in
        links = []
        if ours.rpn(self.flabel) != one.rpn(self.flabel):
            made = self.congruence(one, ours, where, held, None,
                                   self.closing(('toward',)))
            if declined(made):
                return made
            links.append((one, ours, made))
        if said != want:
            if not self.is_wff(ours):
                return Declined('two classes differ in the letters they bind')
            renamed = self.renamed_apart(ours, theirs)
            if renamed is None:
                return Declined('no renaming says the two are one claim')
            links.append((ours, theirs,
                          self.seq(self.seq(said, want, 'wb'), where, renamed,
                                   'a1i')))
        if theirs.rpn(self.flabel) != other.rpn(self.flabel):
            made = self.congruence(other, theirs, where, held, None,
                                   self.closing(('toward',)))
            if declined(made):
                return made
            links.append((theirs, other,
                          self.flipped(where, other, theirs, made)))
        return self.chained(where, links)

    def renamed_apart(self, one, other):
        """A closed proof that two statements differing in their bound
        letters are one, by `renaming`, or by way of letters neither holds
        where one letter is bound twice (`renaming_apart`); else None.
        """
        renamed = self.renaming(one, other)
        if renamed is None:
            renamed = self.renaming_apart(one.rpn(self.flabel),
                                          other.rpn(self.flabel))
        return renamed

    def flipped(self, where, x, y, proof):
        """( where -> y <-> x ), or `=`, from a proof of `x` against `y`."""
        a, b = x.rpn(self.flabel), y.rpn(self.flabel)
        if self.is_wff(x):
            return self.ap('bicomd', {'ph': where, 'ps': a, 'ch': b}, proof)
        return self.ap('eqcomd', {'ph': where, 'A': a, 'B': b}, proof)

    def conditioned(self, one, other, where, held):
        """Two terms a conditional rule makes one, at this place; else None.

        The rule is applied to either side where it stands, what it asks is
        settled here, and what it gives must then have the other side's
        standard form: `nn0absid` takes |N| to N where N is a whole number,
        `rexss` a restriction in the body to one in the domain where the
        one set lies inside the other.
        """
        for label, given, gives, names in self.rewrites(conditional=True):
            for a, b, forward in ((one, other, True), (other, one, False)):
                bound = kernel.match(given, a, {}, names)
                if bound is None or gives.names() - set(bound):
                    continue
                became = gives.substitute(bound)
                ours = self.standard(became).rpn(self.flabel)
                theirs = self.standard(b).rpn(self.flabel)
                if ours != theirs and not self.rebound(ours, theirs):
                    continue
                made = self.standard_proof(a, label, became, where, held)
                if declined(made):
                    continue
                links = [(a, became, made)]
                if became.rpn(self.flabel) != b.rpn(self.flabel):
                    rest = self.congruence(became, b, where, held, None,
                                           self.closing(('standard',)))
                    if declined(rest):
                        continue
                    links.append((became, b, rest))
                proof = self.chained(where, links)
                return proof if forward else self.flipped(where, a, b, proof)
        return None

    # --- a lemma's own substitutions ----------------------------------------

    def substituted_slot(self, asked, binding):
        """A wff slot an essential fixes by saying it is a substitution.

        `elrab` holds a set-builder's body in `ph` and the same body about
        the element in `ps`, and asks `( x = A -> ( ph <-> ps ) )`. Nothing
        on its left side mentions `ps`, so where the claim has not filled it
        this hypothesis is the only thing that says what it is.

        Given only where every other part is settled: the body closed, the
        side being renamed a binder's `cv` over a setvar, and the slot
        still open. A slot standing for itself is open — the match binds a
        lemma's variable to its own name where nothing fixed it, and that
        is what a claim of one half of the right side leaves behind. A
        lemma asking anything else is left alone.
        """
        if asked.label != 'wi' or len(asked.children) != 2:
            return None
        same, iff = asked.children
        if same.label != 'wceq' or iff.label != 'wb':
            return None
        over, element = (one.substitute(binding) for one in same.children)
        body, slot = iff.children
        held = binding.get(slot.variable)
        if (slot.variable is None or over.label != 'cv'
                or over.children[0].variable is None
                or (held is not None and held.variable != slot.variable)
                or body.names() - set(binding)):
            return None
        # The body holds the variable as a binder writes it, `cv` over a
        # setvar; the element is a class. Stripping the `cv` is what lets
        # the one stand in for the other.
        name = over.children[0].variable
        said = self.as_class(body.substitute(binding), {name})
        return {slot.variable: said.substitute({name: element})}

    def witnessed(self, step, wanted, scope, facts, lines):
        """A restricted existential, from the line a step cites for it.

        The text never writes the witness as a witness: it writes a line
        that happens to name one. Bezout's step 2 puts `a` in a set-builder
        whose body is `there are m and n with t = a·m + b·n`, citing
        `a = a·1 + b·0`, and 1 and 0 are the witnesses because that line is
        the body with them in place.

        Taken from the lines the step cites and never searched for among
        the facts in scope. An existential is a step's own claim, so there
        is always a citation to read it off, and settling one by finding
        something that happened to fit would be proving a claim by a route
        the text never names.

        Built from the innermost quantifier out, which is the order the
        witnesses go in: `rspcev` wants the body at one witness and gives
        the existential over it, so the next one out is handed what the
        last one proved.
        """
        layers, rest = [], wanted
        while rest.label == 'wrex':
            body, var, over = rest.children
            layers.append((body, var.rpn(self.flabel),
                           over.rpn(self.flabel)))
            rest = body
        marks = {f'{v} cv' for _b, v, _o in layers}
        for ref in step.just.refs:
            cited = lines.get(ref)
            found = cited and self.witnesses_in(
                rest, self.to_term(cited.term), marks)
            if not found and cited and len(layers) == 1:
                found = self.member_named(cited.term, layers[0])
            if found:
                break
        else:
            raise self.defect(step.line, 'no cited line names a witness for '
                              f'{self.render(wanted.rpn(self.flabel))}')

        # The line that names the witnesses need not be all the claim says
        # of them: `thm:proof/sqrt2-irrational/lowest-terms` exhibits a p and
        # a q that one line says are a fraction in lowest terms, another says
        # is positive, and a third says nothing divides. Where it is all of it, its own
        # proof is taken, because that is fewer steps than settling it.
        proof = facts.get(cited.term, cited.proof)
        innermost = layers[-1][0]
        for _b, v, _o in layers:
            innermost = self.restated(innermost, f'{v} cv', found[f'{v} cv'])
        if innermost.rpn(self.flabel) == 'wtru':
            # A body that says nothing of its variable — S is not empty —
            # holds outright, by the one lemma that states truth.
            proof = self.seq('wtru', scope, 'tru', 'a1i')
        elif innermost.rpn(self.flabel) != cited.term:
            proof = self.settle(innermost, scope, facts, step=step,
                                lines=lines)
            if declined(proof):
                return proof
        for i in reversed(range(len(layers))):
            body, var, over = layers[i]
            mark, held = f'{var} cv', body
            # The quantifiers further out are still open here, and the ones
            # already closed have their witnesses in place.
            for _b, v, _o in layers[:i]:
                held = self.restated(held, f'{v} cv', found[f'{v} cv'])
            witness = found[mark]
            here = self.restated(held, mark, witness)
            ph = held.rpn(self.flabel)
            ps = here.rpn(self.flabel)
            # `rspcev` asks what `elrab` asks — the body before and after,
            # tied by the witness standing where the variable did — so the
            # same branch of `prove_essential` discharges it.
            if ph == ps:
                # The body does not mention the variable, so the witness
                # changes nothing in it: `biidd` says so outright.
                instance = self.seq(seq(mark, witness, 'wceq'), ph, 'biidd')
            else:
                instance = self.prove_essential(
                    self.to_term(self.seq(self.seq(mark, witness, 'wceq'),
                                          self.seq(ph, ps, 'wb'), 'wi')),
                    scope, facts)
                if declined(instance):
                    return instance
            member = self.seq(witness, over, 'wcel')
            proof = self.seq(scope, self.seq(member, ps, 'wa'), self.seq(ph, var, over,
                                                          'wrex'),
                        self.seq(scope, member, ps,
                            self.required(step, member, over, scope, facts),
                            proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev', 'syl')
        return proof

    def member_named(self, said, layer):
        """The witness a line gives by putting something in the domain.

        A "there is s ∈ S" whose body says nothing of s — S is not empty —
        is not matched by what a line says of s, since it says nothing: its
        witness is whatever a cited line puts in S. `check.py` reads the
        same claim the same way, as stated by any fact putting something in
        S; the intermediate value theorem cites `a ∈ S`.
        """
        _body, var, over = layer
        for part in self.parts(said):
            node = self.to_term(part)
            if node.variable is None and node.label == 'wcel' \
                    and node.children[1].rpn(self.flabel) == over:
                return {f'{var} cv': node.children[0].rpn(self.flabel)}
        return None

    def restated(self, term, was, now):
        """`term` with every occurrence of the subterm `was` reading `now`.

        Both are given in reverse Polish, because a term is compared by what
        it spells: the kernel's terms are trees without an equality.
        """
        if term.rpn(self.flabel) == was:
            return self.to_term(now)
        if term.variable is not None:
            return term
        return kernel.Term(term.label,
                           tuple(self.restated(c, was, now)
                                 for c in term.children))

    def read_off(self, sig, binding, variables):
        """What a lemma's naming hypothesis says its own variables are.

        `ralrnmpt` names a map in a hypothesis and speaks of its range in
        the conclusion, so the claim fixes the map and nothing else. What
        the map binds, where that runs and what it builds are read back out
        of it, which is the same move `instanced` makes for a hypothesis
        relating two formulas: the lemma is saying what it means, not
        asking for something.

        What the map binds and builds may appear nowhere else: `elrnmpt1s`
        concludes only that something is in the range, and names the map's
        variable and body in its hypotheses alone. They are the lemma's
        variables all the same, so the naming is read over them too.
        """
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wceq' or len(asked.children) != 2:
                continue
            name = asked.children[0].variable
            if name is None or name not in binding:
                continue
            said = kernel.match(asked.children[1], binding[name],
                                dict(binding),
                                set(variables) | asked.names())
            if said is not None:
                binding = said
        return binding

    def instanced(self, sig, binding):
        """What a lemma asking `( x = A -> ( ph <-> ps ) )` means by `ps`.

        Such a lemma states how its own two sides are related rather than
        asking: `ps` is `ph` with the variable reading the term. `elrab`
        reads a set-builder's body at the element, `rspcev` reads a body at
        a witness, and in both the relation is the lemma's own.

        So it is worked out and not taken from the step. A citation offering
        something else is offering evidence for `ps` rather than `ps`: the
        Bezout proof puts `a` in a set-builder whose body is an existential
        over m and n, citing `a = a·1 + b·0`, and reading that as `ps` asks
        for a biconditional between an existential and one of its instances,
        which is false.

        A hypothesis relating two terms says the same thing of them as one
        relating two formulas says of those: `fsum1` asks `( k = M -> A =
        B )`, and B is the summand read at M.
        """
        out = dict(binding)
        for text in sig.essentials:
            asked = self.syntax.parse(text[1:], 'wff')
            if asked.label != 'wi':
                continue
            at, says = asked.children
            if (at.label != 'wceq' or says.label not in ('wb', 'wceq')
                    or at.children[0].label != 'cv'):
                continue
            name = says.children[1].variable
            if name is None:
                continue
            # Read at a class nothing has fixed yet, the body would be read
            # at the lemma's own variable. `elrnmpt1s` learns what it reads
            # its map at from a line the step cites, which comes later, and
            # the claim has already said what the result is. A set variable
            # left open is different: `f1mpt` reads its map at one, and it
            # stands in the proof as a name of its own.
            kinds = dict((v, t) for t, v in sig.floats)
            if any(kinds.get(v) == 'class' for v in at.names() - set(out)):
                continue
            was, now = (c.substitute(out).rpn(self.flabel)
                        for c in at.children)
            out[name] = self.restated(says.children[0].substitute(out),
                                      was, now)
        return out

    # --- one claim spelt two ways -------------------------------------------

    def bridging(self, given, want, scope, facts, step):
        """A proof that two terms written differently agree.

        set.mm writes `( k x. 2 )` where the corpus writes 2k, and those are
        the same number but not the same formula: `same` says so.
        """
        return self.same(given, want, scope, facts, step)

    def renaming(self, given, want):
        """The two as one claim, spelt with different bound variables.

        A `define` renames what its body binds, because the proof may go on
        to fix a name spelt the same way: Bezout's S binds a j where the
        step that reads it writes an n. `cbvrexvw` is set.mm saying those
        are one claim, and `cbvrexv` says it too by way of ax-13, which
        set.mm discourages.

        Closed, and lifted by closed lemmas. `rexbidva` would carry the
        scope under the binder and forbids the binder in what it carries,
        and the scope here names the very set-builder whose body binds it.
        None of this wants a scope: the two are one claim wherever they
        stand.
        """
        if given.rpn(self.flabel) == want.rpn(self.flabel):
            return None                        # nothing is spelt differently
        if (given.label != want.label
                or len(given.children) != len(want.children)):
            return None
        under = rules.BOUND.get(given.label)
        if under is not None:
            same, cross, over = *under, None
            if len(given.children) == 3:
                body, variable, over = given.children
                other, renamed, runs = want.children
                if over.rpn(self.flabel) != runs.rpn(self.flabel):
                    return None
            else:
                (body, variable), (other, renamed) = (given.children,
                                                      want.children)
            binds = {'ph': body.rpn(self.flabel),
                     'ps': other.rpn(self.flabel),
                     'x': variable.rpn(self.flabel)}
            if over is not None:
                binds['A'] = over.rpn(self.flabel)

            def bound(said, at=binds['x'], runs=over):
                """One binder put back around a body."""
                return (self.seq(said, at, runs.rpn(self.flabel), given.label)
                        if runs is not None else self.seq(said, at, given.label))

            if variable.variable == renamed.variable:
                inner = self.renaming(body, other)
                return None if inner is None else self.ap(same, binds, inner)
            # The cross lemma changes one binder and wants a hypothesis
            # relating the two bodies at x = y, which a body still spelt
            # two ways inside is not. So the bodies are made to agree
            # first, over this binder as it stands, and only then is it
            # changed.
            here = self.restated(other, f'{renamed.rpn(self.flabel)} cv',
                                 f'{variable.rpn(self.flabel)} cv')
            middle = dict(binds, ph=here.rpn(self.flabel))
            at = self.seq(self.seq(f'{variable.rpn(self.flabel)} cv',
                         f'{renamed.rpn(self.flabel)} cv', 'wceq'),
                     self.seq(middle['ph'], binds['ps'], 'wb'), 'wi')
            said = self.prove_essential(self.to_term(at), '', {})
            if declined(said):
                return None
            changed = self.ap(cross, dict(
                middle, y=renamed.rpn(self.flabel)), said)
            if middle['ph'] == binds['ph']:
                return changed
            inner = self.renaming(body, here)
            if inner is None:
                return None
            agreed = self.ap(same, dict(binds, ps=middle['ph']), inner)
            return self.ap('bitri', {'ph': bound(binds['ph']),
                                     'ps': bound(middle['ph']),
                                     'ch': want.rpn(self.flabel)},
                           agreed, changed)
        spelt = [c.rpn(self.flabel) for c in given.children]
        other = [c.rpn(self.flabel) for c in want.children]
        # Both halves of an implication may be spelt differently at once —
        # an induction's step claims P(k) -> P(k+1) in the part's own name
        # where the lemma wants the pattern's. The lifters each change one
        # side and hold the other, so the sides are changed one at a time
        # and the halfway claim is what joins the two.
        here, start, proof = list(spelt), self.seq(*spelt, given.label), None
        for slot in (i for i in range(len(spelt)) if spelt[i] != other[i]):
            label = rules.RENAMED.get((given.label, (slot,)))
            if label is None:
                return None
            inner = self.renaming(given.children[slot], want.children[slot])
            if inner is None:
                return None
            rest = here[1] if slot == 0 else here[0]
            step = self.ap(label, {'ph': here[slot], 'ps': other[slot],
                                   'ch': rest}, inner)
            was = self.seq(*here, given.label)
            here[slot] = other[slot]
            if proof is None:
                proof = step
                continue
            proof = self.ap('bitri', {'ph': start, 'ps': was,
                                      'ch': self.seq(*here, given.label)},
                            proof, step)
        return proof

    def respelt(self, proof, said, want, scope):
        """A proof of a claim, made a proof of it spelt another way.

        Two places in a proof may bind one name under two words, because
        each is written where different words were already taken. What is
        proved is the same claim, and `same` is what says so; it asks
        nothing of the scope, since a renaming or a rewriting rule that asks
        nothing is all the two can differ by here.
        """
        if said == want:
            return proof
        alike = self.same(self.to_term(said), self.to_term(want), scope, {})
        if declined(alike):
            return None
        return self.seq(scope, said, want, proof, alike, 'mpbid')

    def renaming_apart(self, said, want):
        """`renaming` by way of letters neither statement holds.

        `renaming` changes the outer binder first, restating the body it
        wants at the old letter, and that is wrong where the old letter is
        bound again further in: `elcncf2` binds x outside and w inside,
        and the page binds c′ outside and x inside, so restating the page's
        body with x for c′ puts two binders on one letter. Every letter the
        first statement binds is moved to one nothing holds, and the
        statement is renamed from there, where nothing can be caught.

        The letters are only looked at, not taken. They stand in the middle
        of one closed equivalence and nowhere else, and this is tried
        wherever a plain renaming fails, which taking them each time would
        spend the proof's spare letters on.
        """
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values())
                | set(said.split()) | set(want.split()))
        free = iter(v for v in self.spare if v not in held)
        moved, rest = {}, [self.to_term(said)]
        while rest:
            node = rest.pop()
            if node.label in rules.BOUND and len(node.children) >= 2:
                letter = node.children[1].variable
                if letter is not None and letter not in moved:
                    fresh = next(free, None)
                    if fresh is None:
                        return None
                    moved[letter] = kernel.Term(
                        variable=self.sigs[fresh].statement[1])
            rest.extend(node.children)
        if not moved:
            return None
        middle = self.to_term(said).substitute(moved)
        there = self.renaming(self.to_term(said), middle)
        back = self.renaming(middle, self.to_term(want))
        if there is None or back is None:
            return None
        return self.ap('bitri', {'ph': said, 'ps': middle.rpn(self.flabel),
                                 'ch': want}, there, back)

    def letters_apart(self, label, goal, scope, facts, step, crossing, seed):
        """A lemma that binds two letters apart, where the claim binds one.

        `fsumshft` re-indexes a sum and names the index j on one side and k
        on the other, and keeps them apart; the page writes k on both, as
        a reader does, since what a sum binds is no part of what it is. So
        the sum on the right is renamed to a letter nothing holds, the
        lemma proves that, and `cbvsumv` says the two sums are one. The
        letter is only looked at, not taken: it stands in this proof and
        nowhere else.
        """
        if goal.label != 'wceq' or goal.children[1].label != 'csu':
            return Declined(f'{label} binds two letters apart where the claim '
                            f'binds one, and the claim is not an equation '
                            f'with a sum on its right')
        left, right = goal.children
        limits, summand, index = right.children
        held = ({t.split()[0] for t in self.names.values()
                 if isinstance(t, str) and t.endswith(' cv')}
                | self.reserved | set(self.bound_as.values())
                | set(goal.rpn(self.flabel).split()))
        free = next((v for v in self.spare if v not in held), None)
        if free is None:
            return Declined('no letter left to rename a sum with')
        letter = kernel.Term(variable=self.sigs[free].statement[1])
        moved = summand.substitute({index.variable: letter})
        renamed = kernel.Term('csu', (limits, moved, letter))
        first = self.apply_lemma(
            label, kernel.Term('wceq', (left, renamed)), scope, facts, step,
            crossing, seed)
        if declined(first):
            return first
        tie = self.prove_essential(
            kernel.Term('wi', (kernel.Term('wceq', (
                kernel.Term('cv', (letter,)), kernel.Term('cv', (index,)))),
                kernel.Term('wceq', (moved, summand)))), scope, facts)
        if declined(tie):
            return tie
        same = self.ap('cbvsumv', {'j': letter.rpn(self.flabel),
                                   'k': index.rpn(self.flabel),
                                   'A': limits.rpn(self.flabel),
                                   'B': moved.rpn(self.flabel),
                                   'C': summand.rpn(self.flabel)}, tie)
        was, now = renamed.rpn(self.flabel), right.rpn(self.flabel)
        return self.ap('eqtrd', {'ph': scope, 'A': left.rpn(self.flabel),
                                 'B': was, 'C': now},
                       first, self.seq(self.seq(was, now, 'wceq'), scope,
                                       same, 'a1i'))

    # --- one lemma ----------------------------------------------------------

    def through_existential(self, label, whole, reads, goal, scope, facts,
                            step, seed):
        """A lemma's existential taken apart, and the claim's put back.

        `divalg` says there is exactly one remainder, quantified the other
        way round, bounding by the absolute value, and saying its three
        things in a different order. The division algorithm as a reader
        writes it says the same. Two of those four differences stop being
        differences once the quantifier is off: in the open `unpack` makes
        the body's parts facts and `settle` puts them back in whatever
        order the claim asks, and there is no order to quantifiers that are
        not there.

        So the lemma's existential is proved, weakened where it says
        exactly one, eliminated, and the claim introduced at the variables
        it gave up. `obtain` does the eliminating for a step, deferring the
        discharge because only the main loop knows a goal; here the goal is
        in hand and nothing is deferred.
        """
        if goal.label != 'wrex' or reads.label not in ('wrex', 'wreu'):
            return Declined(f'{label} and the claim are not both "there is"')
        if seed is None or (reads.names() - set(seed)
                            - set(self.bound_in(reads))):
            return Declined(f'nothing fixes the variables of {label}')
        ground = reads.substitute(seed)
        # The lemma's binders become names in the open, so they must be
        # variables nothing else holds — and the claim's own binders are
        # among what is held, because `rspcev` will not take a witness that
        # mentions the binder it is introducing. `divalg` binds q and r and
        # so does the division algorithm as a reader writes it, which is
        # what makes this not the corner case it looks like.
        taken, swap = self.bound_in(goal), {}
        for name in self.bound_in(ground):
            fresh = self.spare_var()
            while self.sigs[fresh].statement[1] in taken:
                fresh = self.spare_var()
            swap[name] = kernel.Term(variable=self.sigs[fresh].statement[1])
        ground = ground.substitute(swap)
        strong = self.apply_lemma(label, ground, scope, facts, step,
                                  crossing=False, seed=seed)
        if declined(strong):
            return strong
        if ground.label == 'wreu':
            weaker = kernel.Term('wrex', tuple(ground.children))
            body, var, over = ground.children
            strong = self.seq(scope, ground.rpn(self.flabel),
                         weaker.rpn(self.flabel), strong,
                         self.ap('reurex', {'ph': body.rpn(self.flabel),
                                            'x': var.rpn(self.flabel),
                                            'A': over.rpn(self.flabel)}),
                         'syl')
            ground = weaker

        layers, rest = [], ground
        while rest.label == 'wrex':
            _body, var, over = rest.children
            layers.append((var.rpn(self.flabel), over.rpn(self.flabel)))
            rest = _body
        body = rest.rpn(self.flabel)
        member = self.seq(*(self.seq(f'{v} cv', s, 'wcel') for v, s in layers))
        if len(layers) > 1:
            member = self.seq(member, 'wa')

        with self.frames_kept():
            outer, held = self.widen(scope, facts, member)
            inner, lifted = self.widen(outer, held, body)
            made = self.introduced(goal, inner, lifted)
        if declined(made):
            return made
        want = goal.rpn(self.flabel)
        discharge = 'rexlimdva' if len(layers) == 1 else 'rexlimdvva'
        pushed = [v for v, _s in layers] + [s for _v, s in layers]
        return self.seq(scope, ground.rpn(self.flabel), want, strong,
                   self.seq(scope, body, want, *pushed,
                       self.seq(outer, body, want, made, 'ex'), discharge),
                   'mpd')

    def from_lemmas(self, labels, goal, scope, facts, step, seed):
        """An existence claim its item's lemmas together give.

        `thm:proof/sqrt2-irrational/lowest-terms` says a rational is some p
        over some q with nothing above 1 dividing both. set.mm says that of
        the numerator and denominator it names for a rational, in three
        theorems and no existential at all: what they are is `qnumdencl`, that
        the rational is their quotient is `qeqnumdivden`, and that they are
        coprime is `qnumdencoprm`.

        So each is proved at what the `with` target says it is about, and
        the claim introduced at the terms they turn out to be about. The
        lemmas are the ones the database names and the witnesses are read
        off them, which is what keeps this from being a search.
        """
        if not labels or not seed:
            return Declined('no `with` target says what the lemmas are about')
        want = self.to_term(goal)
        if want.label != 'wrex':
            return Declined('the claim is not "there is"')
        if any(label not in self.sigs for label in labels):
            return Declined(f'{", ".join(labels)} are not all in the library')
        theirs = {v for label in labels for v in self.sigs[label].push}
        witness = [name for name in seed if name not in theirs]
        if witness:
            return self.at_witness(labels, want, seed, witness, scope, facts,
                                   step)
        known = dict(facts)
        for label in labels:
            sig = self.sigs.get(label)
            if sig is None:
                return Declined(f'{label} is not in the library')
            reads = self.syntax.statement(sig)
            while reads.label == 'wi':
                reads = reads.children[1]
            if reads.names() - set(seed):
                return Declined(f'the target does not say what {label} is '
                                f'about')
            said = reads.substitute(seed).rpn(self.flabel)
            proof = self.apply_lemma(label, self.to_term(said), scope, facts,
                                     step, crossing=False, seed=seed)
            if declined(proof):
                return proof
            known[said] = proof
            self.unpack(said, proof, scope, known)
        return self.introduced(want, scope, known)

    def at_witness(self, labels, want, seed, witness, scope, facts, step):
        """An existence claim at the thing a `with` target names for it.

        `thm:stdlib/calculus/completeness` says there is a least upper bound, and set.mm
        names one: the supremum. What the claim asks of it — that it is
        real, that nothing in the set is above it, that it is at most
        anything nothing in the set is above — is one lemma each, and each
        is said of one element or one bound at a time, which `as_generalised`
        says of every one. So the witness is put in for the binder, each
        part of what the claim then says is proved by the first lemma that
        reaches it, and the claim is introduced at the witness.

        A `with` name that is none of the lemmas' variables is what says
        this: it can only be the claim's own binder.
        """
        if len(witness) != 1:
            return Declined(f'the target names {len(witness)} witnesses '
                            f'and the claim is read one binder at a time')
        body, variable, over = want.children
        stood = seed[witness[0]]
        member = self.seq(stood.rpn(self.flabel), over.rpn(self.flabel),
                          'wcel')
        said = self.replaced(body, f'{variable.rpn(self.flabel)} cv', stood)

        def by_lemmas(one):
            refused = []
            for label in labels:
                made = self.apply_lemma(label, one, scope, facts, step)
                if not declined(made):
                    return made
                refused.append(f'{label}: {made}')
            return Declined('; '.join(refused))

        known = dict(facts)
        for part in (self.to_term(member), said):
            made = self.conjoined(part, scope, by_lemmas)
            if made is None:
                made = by_lemmas(part)
            if declined(made):
                return made
            known[part.rpn(self.flabel)] = made
            self.unpack(part.rpn(self.flabel), made, scope, known)
        return self.introduced(want, scope, known)

    def as_class(self, node, marks):
        """A pattern whose binders stand for whatever class fills them.

        A binder is written `cv` over a setvar, which matches a setvar and
        nothing else. What a claim quantifies over may be answered by a
        term — a rational's numerator is one — and the name is the claim's
        way of writing it, not a constraint on what it is.
        """
        if node.variable is not None:
            return node
        if node.label == 'cv' and node.children[0].variable in marks:
            return node.children[0]
        return kernel.Term(node.label, tuple(self.as_class(one, marks)
                                             for one in node.children))

    def introduced(self, goal, scope, facts):
        """An existential claim at witnesses the scope already names.

        `witnessed` does this shape from the lines a step cites. Here the
        witnesses are whatever the elimination just gave up, and which of
        them stands for which binder is read off the body: one part of the
        claim matched against one fact in scope fixes them all, because
        every binder occurs in the part that mentions them.

        A witness may be a term and not a name. `qeqnumdivden` says a
        rational is its numerator over its denominator, and matching a
        claim's `x = p / q` against it is what says that p and q stand for
        those two — so the binder is matched as the class it stands for
        rather than as the name it is written with.
        """
        marks, rest = [], goal
        while rest.label == 'wrex':
            marks.append(rest.children[1].variable)
            rest = rest.children[0]
        found = None
        for piece in self.parts(rest.rpn(self.flabel)):
            shape = self.as_class(self.to_term(piece), set(marks))
            for said in facts:
                fits = kernel.match(shape, self.to_term(said), {}, set(marks))
                if fits is not None and len(fits) == len(marks):
                    found = fits
                    break
            if found is not None:
                break
        if found is None:
            return Declined('no fact in scope names what the claim binds')
        # What each binder stands for, as `rspcev` wants it: a class. One
        # matched where it was written keeps the `cv` that made it one.
        stood = {}
        for name, term in found.items():
            said = term.rpn(self.flabel)
            stood[name] = (self.seq(said, 'cv')
                           if term.variable is not None else said)

        layers, rest = [], goal
        while rest.label == 'wrex':
            body, var, over = rest.children
            layers.append((body, var.variable, over.rpn(self.flabel)))
            rest = body

        proof = None
        for i in reversed(range(len(layers))):
            body, name, over = layers[i]
            # The body with every binder outside this one already standing
            # at its witness, and then with this one too. Put in place of
            # the name where it stands rather than substituted for it: a
            # witness that is a term is not a setvar, and substituting one
            # for the other would leave the `cv` standing over a class.
            var = self.flabel[name]
            held = body
            for _b, n, _o in layers[:i]:
                held = self.restated(held, f'{self.flabel[n]} cv', stood[n])
            here = self.restated(held, f'{var} cv', stood[name])
            ph, ps = held.rpn(self.flabel), here.rpn(self.flabel)
            if proof is None:
                proof = self.settle(here, scope, facts)
                if declined(proof):
                    return proof
            witness = stood[name]
            instance = self.prove_essential(
                self.to_term(self.seq(self.seq(f'{var} cv', witness, 'wceq'),
                                 self.seq(ph, ps, 'wb'), 'wi')), scope, facts)
            if declined(instance):
                return instance
            member = self.seq(witness, over, 'wcel')
            stands = self.settle(self.to_term(member), scope, facts)
            if declined(stands):
                return stands
            proof = self.seq(scope, self.seq(member, ps, 'wa'),
                        self.seq(ph, var, over, 'wrex'),
                        self.seq(scope, member, ps, stands, proof, 'jca'),
                        ph, ps, var, witness, over, instance, 'rspcev',
                        'syl')
        return proof

    def as_generalised(self, label, goal, scope, facts, step, seed):
        """A lemma said of every such name.

        `dvdslegcd` says a common divisor is no greater than the gcd, of
        whatever divisor it is given, and `def:stdlib/divisibility/gcd` says it
        of every e in ℕ. The name is fixed, the lemma applied to it, and `ralrimiva`
        gives it back — the same move a `fix` block closes with, over a
        lemma rather than over a block.
        """
        if goal.label != 'wral':
            return Declined('the claim is not "for every"')
        body, variable, over = goal.children
        member = self.seq(f'{variable.rpn(self.flabel)} cv',
                     over.rpn(self.flabel), 'wcel')
        with self.frames_kept():
            inner, lifted = self.widen(scope, facts, member)
            proof = self.apply_lemma(label, body, inner, lifted, step,
                                     crossing=False, seed=seed)
        if declined(proof):
            return proof
        return self.seq(scope, body.rpn(self.flabel), variable.rpn(self.flabel),
                   over.rpn(self.flabel), proof, 'ralrimiva')

    def as_conjunct(self, label, whole, reads, goal, scope, facts, step, seed):
        """One half of what a lemma concludes.

        `gcddvds` says in one conjunction that a gcd divides both its
        arguments, and `def:stdlib/divisibility/gcd` states those as two
        sentences because a reader reads them as two. The half the claim is
        fixes the lemma, and `simpld` or `simprd` takes it.
        """
        if reads.label != 'wa' or len(reads.children) != 2:
            return Declined(f'{label} does not conclude a conjunction')
        asks, walk = [], whole
        while walk.label in ('wi', 'wb') and walk is not reads:
            asks.append(walk.children[0])
            walk = walk.children[1]
        for i, part in enumerate(reads.children):
            bound = kernel.match(part, goal, dict(seed or {}), whole.names())
            if bound is None:
                continue
            # A half need not name everything the lemma does: `ssdifsn` says
            # what is not in the subset without saying what it is a subset
            # of, and what is left open is what the step cited a line for.
            for slot in asks:
                if not reads.names() - set(bound):
                    break
                for held in facts:
                    filled = kernel.match(slot, self.to_term(held),
                                          dict(bound), whole.names())
                    if filled is not None:
                        bound = filled
                        break
            if reads.names() - set(bound):
                continue
            said = reads.substitute(bound)
            proof = self.apply_lemma(label, said, scope, facts, step,
                                     crossing=False, seed=bound)
            if declined(proof):
                continue
            a, b = (one.rpn(self.flabel) for one in said.children)
            return self.seq(scope, a, b, proof, 'simpld' if i == 0 else 'simprd')
        return Declined(f'neither half of what {label} concludes is the claim')

    def as_seeded(self, label, reads, goal, scope, facts, step, seed):
        """A lemma whose `with` target already says what it concludes.

        Where the seed fixes every variable there is nothing left for the
        claim to fix, and the two need not be spelt the same: `dvds2ln`
        writes the multiplier before the number being divided and the
        corpus writes it after, so what the lemma gives is what the step
        claims with each product exchanged. `db/notation.records` declares
        that the product may be, and `bridging` carries it.

        Only with a full seed. A claim left to fix a variable is a claim
        the conclusion has to match, or the lemma would be applied at
        whatever made the bridge work rather than at what the item says.
        """
        if seed is None or reads.names() - set(seed):
            return Declined(f'the target does not fix every variable of '
                            f'{label}')
        said = reads.substitute(seed)
        if said.rpn(self.flabel) == goal.rpn(self.flabel):
            return Declined(f'{label} at its seed is the claim as written')
        proof = self.apply_lemma(label, said, scope, facts, step,
                                 crossing=False, seed=seed)
        if declined(proof):
            return proof
        # No bridge means the lemma is not this claim said otherwise. A
        # target may name several lemmas, each giving a part of what the
        # item says, and then none of them is.
        across = self.bridging(said, goal, scope, facts, step)
        if declined(across):
            across = self.by_equation(said, goal, scope, facts, step)
        if across is None or declined(across):
            return Declined(f'nothing carries what {label} gives to the claim')
        return self.seq(scope, said.rpn(self.flabel), goal.rpn(self.flabel), proof,
                   across, 'mpbid')

    def by_equation(self, said, goal, scope, facts, step):
        """A lemma's conclusion carried to the claim by an equation proved.

        `hashun` says the size of a disjoint union is the sum of the two
        sizes; `thm:stdlib/counting/card-disjoint-union` assumes each size is
        a number and states the claim in those numbers, so what stands between the two
        is the equations the item assumes. The step cites the lines that
        prove them — `substitute` is the readable method for the same
        rewrite, and the text writes no step for it here because the item
        already said which equations are in play.

        The walk decides where to ask, so nothing is looked for: each place
        the two terms differ is one equation, and it is settled where it
        stands. A difference the scope does not prove is not a route.
        """
        proved = self.closing(('held',))
        straight = self.congruence(said, goal, scope, facts, step, proved)
        if not declined(straight):
            return straight
        if goal.label != 'wceq' or len(goal.children) != 2:
            return None
        # An equation is the same equation written the other way round, and
        # a lemma need not write it the way the item states it: `hashen`
        # equates the size already known with the size being asked for, and
        # the step claims the second of them. `eqcom` is closed, so it
        # crosses into the scope rather than being proved inside it.
        turned = kernel.Term('wceq', goal.children[::-1])
        across = self.congruence(said, turned, scope, facts, step, proved)
        if declined(across):
            return None
        back = self.same(turned, goal, scope, facts, step)
        if declined(back):
            return None
        return self.chained(scope, [(said, turned, across),
                                    (turned, goal, back)])

    def crossed(self, label, whole, reads, goal, scope, facts, step):
        """A lemma reaching a claim set.mm says is the same claim.

        `exprmfct` says there is a prime dividing a number; the readable
        line says there is a natural number, prime, dividing it. Those are
        one statement written two ways, and `rexss` is set.mm saying so:
        quantifying over a subset is quantifying over the set with
        membership of the subset moved into the body.

        So where what a lemma concludes is not what is wanted, a declared
        biconditional is asked whether the two are the same thing. The goal
        is ground, so matching one side of the bridge against it fixes the
        bridge; the other side is then determined, and matching that against
        the lemma's conclusion fixes what the goal could not.

        The bridge comes from `rules.MEMBERSHIP` and nowhere else, which
        is the rule that stops an elaborator reaching a claim by whatever it
        can find that fits.
        """
        variables = whole.names()
        want = goal.rpn(self.flabel)
        for bridge in self.declared_as('equivalence'):
            says = self.syntax.statement(self.sigs[bridge])
            names = says.names()
            while says.label == 'wi':
                says = says.children[1]
            for near, far in (says.children, says.children[::-1]):
                bound = kernel.match(far, goal, {}, names)
                if bound is None:
                    continue
                # A side the goal did not fix would leave the bridge's own
                # variable standing in what is proved. Asked of the side
                # rather than of the result: the proof has names of its own
                # and one of them is spelt `A`, which is also what `rexss`
                # calls the set it quantifies over.
                if near.names() - set(bound):
                    continue
                candidate = near.substitute(bound)
                if kernel.match(reads, candidate, {}, variables) is None:
                    continue
                said = candidate.rpn(self.flabel)
                found = self.apply_lemma(label, candidate, scope, facts,
                                         step, crossing=False)
                if declined(found):
                    continue
                alike = self.settle(self.to_term(self.seq(said, want, 'wb')),
                                    scope, facts)
                if declined(alike):
                    continue
                return self.seq(scope, said, want, found, alike, 'mpbid')
        return Declined(f'no declared biconditional carries what {label} '
                        f'concludes to the claim')

    def sethood(self, slot, binding):
        """The classes an antecedent asks about and nothing decides.

        `hashsng` asks `A e. V` and concludes about `{ A }`, so nothing it
        says fixes the class; `hashvnfin` asks it inside a conjunction and
        is the same. set.mm leaves such a class free so that a citation may
        name any class holding A, and what it is asking is that A be a set.
        `_V` is how that is written, and the weakest class there is to
        write, so nothing is lost by writing it.

        Read only after the conclusion and the scope have both been asked,
        so a class the step does decide is decided by the step.
        """
        out, rest = [], [slot]
        while rest:
            node = rest.pop()
            if node.label == 'wa':
                rest.extend(node.children)
                continue
            if node.label in ('wral', 'wal'):
                rest.append(node.children[0])
                continue
            # Where a map's values land is the same kind of question as where
            # a set lives, and set.mm asks it the same way: `f1f1orn` wants a
            # codomain and says nothing about it, because being one-to-one
            # into one class is being one-to-one into any that holds the
            # values. `_V` holds them all.
            at = {'wcel': 1, 'wf': 1, 'wf1': 1, 'wfo': 1, 'wf1o': 1}.get(
                node.label)
            if at is None:
                continue
            name = node.children[at].variable
            if name is not None and name not in binding:
                out.append(name)
        return out

    def apply_lemma(self, label, goal, scope, facts, step, crossing=True,
                    seed=None):
        """Apply one set.mm lemma to reach a claim, side conditions and all.

        What a lemma states before the claim it reaches may be an
        implication or a biconditional: `dvds1` says that on ℕ0, dividing
        one and being one are the same, and a step citing it has the
        dividing and wants the being. Both are peeled, and which one each
        was decides how it is discharged.

        `seed` is what a `with` target said the lemma's variables stand
        for. The match confirms it where the conclusion is the claim, and
        supplies it where the conclusion is the claim said differently and
        so fixes nothing.
        """
        sig = self.sigs[label]
        whole = self.syntax.statement(sig)
        variables = whole.names()
        # The readable "a or b or c" is built from the left, and set.mm
        # states a three-way disjunction as one constructor: `lttri4` says
        # A < B, A = B or B < A with `w3o`. `df-3or` says they are the same.
        ends = whole
        while ends.label in ('wi', 'wb'):
            ends = ends.children[1]
        if (ends.label == 'w3o' and goal.label == 'wo'
                and goal.children[0].label == 'wo'):
            three = [*(c.rpn(self.flabel) for c in goal.children[0].children),
                     goal.children[1].rpn(self.flabel)]
            said = self.seq(*three, 'w3o')
            got = self.apply_lemma(label, self.to_term(said), scope, facts,
                                   step, crossing, seed)
            if declined(got):
                return got
            return self.seq(scope, said, goal.rpn(self.flabel), got,
                            self.seq(*three, 'df-3or'), 'sylib')
        antecedents, joins, reads, binding = [], [], whole, None
        while True:
            binding = kernel.match(reads, goal, dict(seed or {}), variables)
            if binding is not None:
                break
            if reads.label not in ('wi', 'wb'):
                if crossing:
                    through = self.through_existential(
                        label, whole, reads, goal, scope, facts, step, seed)
                    if not declined(through):
                        return through
                    seeded = self.as_seeded(label, reads, goal, scope, facts,
                                            step, seed)
                    if not declined(seeded):
                        return seeded
                    part = self.as_conjunct(label, whole, reads, goal, scope,
                                            facts, step, seed)
                    if not declined(part):
                        return part
                    every = self.as_generalised(label, goal, scope, facts,
                                                step, seed)
                    if not declined(every):
                        return every
                    return self.crossed(label, whole, reads, goal, scope,
                                        facts, step)
                return Declined(f'{label} does not conclude the claim')
            # A biconditional says one thing and reaching it either way is
            # reaching it: `elnnz` says a natural number is an integer above
            # zero, and a step with the integer and the bound wants the
            # natural number, which is the side a forward read peels off.
            # Tried only where the forward read has already failed, so a
            # lemma that fits as it stands fits as it always did.
            if reads.label == 'wb':
                # With the seed, as the forward read is: `halfpos2` says
                # 0 < A exactly when 0 < A / 2, and the claim 0 < δ / 2
                # fits the near side at A := δ / 2 unless the target says A
                # is δ.
                turned = kernel.match(reads.children[0], goal,
                                      dict(seed or {}), variables)
                if turned is not None:
                    antecedents.append(reads.children[1])
                    joins.append(TURNED)
                    binding, reads = turned, reads.children[0]
                    break
                # The near side may be the claim said differently, and only
                # a full seed can tell: `hashen` equates two sizes and the
                # step claims one of them, so nothing in the goal matches
                # either side and nothing in it fixes the lemma's classes.
                if crossing:
                    seeded = self.as_seeded(label, reads.children[0], goal,
                                            scope, facts, step, seed)
                    if not declined(seeded):
                        return seeded
                # One way of the biconditional may be the claim: `suprleub`
                # says the supremum is at most B exactly when nothing in the
                # set is above B, and a least upper bound is at most every
                # such B, which is the way from the second to the first.
                if goal.label == 'wi':
                    taken = self.one_direction(label, reads, goal, variables,
                                               scope, facts, step, crossing,
                                               seed)
                    if not declined(taken):
                        return taken
            antecedents.append(reads.children[0])
            joins.append(reads.label)
            reads = reads.children[1]

        # A lemma whose hypothesis says what one of its variables is has
        # already decided it, and the match reads the claim's answer over
        # the top. Where the two disagree the claim is not what the lemma
        # concludes, so the lemma is proved at its own value instead. What
        # a naming hypothesis decides comes first, because what a relating
        # one says is said of it.
        binding = self.read_off(sig, binding, variables)
        settled = self.instanced(sig, binding)
        if any(settled[name].rpn(self.flabel) != stood.rpn(self.flabel)
               for name, stood in binding.items()):
            return self.at_its_own_value(label, sig, goal, scope, facts,
                                         step, settled)
        # Agreeing, it is also what the lemma says of the side the claim did
        # not fix, and a biconditional crossed the other way leaves that
        # side for the hypothesis to decide.
        binding = settled
        # Two letters the lemma binds and keeps apart, which the claim spells
        # alike, cannot both be the claim's: the lemma is used with one of
        # them renamed (`letters_apart`).
        kinds = {v: t for t, v in sig.floats}
        if any(kinds.get(a) == 'setvar' == kinds.get(b)
               and a in binding and b in binding
               and binding[a].rpn(self.flabel) == binding[b].rpn(self.flabel)
               for a, b in sig.disjoint):
            return self.letters_apart(label, goal, scope, facts, step,
                                      crossing, seed)
        # The scope is where a lemma's disjointness conditions can forbid it,
        # so it is chosen before anything is built. ELABORATION.md 14.
        where, frame = self.allowed(sig, binding, variables)
        if declined(where):
            # Which scope is allowed depends on what the variables stand
            # for. `ralrnmpt` forbids its own binder in the property it
            # carries, and until a cited line fixes that binder every scope
            # holding the property looks forbidden. So what the facts decide
            # is read and the question asked again — only here, because
            # binding early changes which fact answers an antecedent.
            for slot in antecedents:
                if not slot.names() - set(binding):
                    continue
                for held in facts:
                    filled = kernel.match(slot, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            where, frame = self.allowed(sig, binding, variables)
            if declined(where):
                return where
        known = self.with_cited(
            step, where, self.supplied(step, where,
                                       self.frames_facts(frame, facts)))
        for slot in antecedents:
            if not slot.names() - set(binding):
                continue
            if slot.variable is not None:
                binding[slot.variable] = self.to_term(where)
                continue
            # What the lemma concludes need not fix everything it asks, so
            # an antecedent that is still open is matched against something
            # the step already has: `orel2` learns which disjunct is ruled
            # out from the line that rules it out. One that asks several
            # things at once is matched a conjunct at a time, since each is
            # a line of its own: `sstr` asks A ⊆ B and B ⊆ C, and only the
            # lines say what B is.
            for piece in self.conjuncts_of(slot):
                if not piece.names() - set(binding):
                    continue
                for held in known:
                    filled = kernel.match(piece, self.to_term(held),
                                          dict(binding), variables)
                    if filled is not None:
                        binding = filled
                        break
            for open_class in self.sethood(slot, binding):
                binding[open_class] = self.to_term('cvv')
        essentials = [self.prove_essential(
            self.syntax.parse(e[1:], 'wff').substitute(binding), where, known)
            for e in sig.essentials]
        for one in essentials:
            if declined(one):
                return one
        proof = self.ap(label, self.spelt(binding), *essentials)
        if not antecedents:
            # The lemma asks nothing, so it states the claim outright and has
            # to be brought into the scope the step sits in.
            return self.carry(self.seq(goal.rpn(self.flabel), where, proof, 'a1i'),
                              goal.rpn(self.flabel), frame)
        carried = stood_under = False
        for i, slot in enumerate(antecedents):
            asks = slot.substitute(binding)
            if asks.rpn(self.flabel) == where:
                carried = True
                # A variable slot is the context a deduction-form lemma is
                # stated in, and uses nothing; a formula the scope happens to
                # be is what the lemma asks, and uses all of it.
                stood_under = stood_under or slot.variable is None
                continue                      # the deduction slot
            rest = goal.rpn(self.flabel)
            for later, join in reversed(list(zip(antecedents[i + 1:],
                                                 joins[i + 1:], strict=True))):
                if later.substitute(binding).rpn(self.flabel) != where:
                    said = later.substitute(binding).rpn(self.flabel)
                    # A biconditional crossed the other way puts the claim
                    # on the left, where every other join puts what is asked
                    # on the left: `hashen` asks two sets be finite and then
                    # equates their sizes with a bijection, and reaching the
                    # sizes from the bijection reads it right to left.
                    rest = (self.seq(rest, said, 'wb') if join is TURNED
                            else self.seq(said, rest, join))
            # What decides the fold is whether what has been built so far
            # states its claim outright or states it under the scope. The
            # bare lemma states it outright — unless one of its own
            # antecedents was the scope, which `ssneld` does: it asks for
            # the inclusion under the scope and then says, still under it,
            # that what is outside the larger set is outside the smaller.
            first = proof.text.rsplit(None, 1)[-1] == label and not carried
            # `mpbird` names the two sides in the order it states them, and
            # a crossed biconditional states the claim first; every other
            # fold states what is asked first.
            sides = ((rest, asks.rpn(self.flabel))
                     if joins[i] is TURNED and not first
                     else (asks.rpn(self.flabel), rest))
            # A "there is" the lemma asks can be given by an instance a line
            # the step cites names: `suprcl` asks that S be bounded above,
            # and step 8 of the intermediate value proof cites that b is an
            # upper bound. Only then is the step passed, so every other side
            # condition is settled from declared lemmas as before.
            instanced = any(self.to_term(part).label == 'wrex'
                            for part in self.parts(asks.rpn(self.flabel)))
            under = (self.settle(asks, where, known, step=step,
                                 lines=self.lines)
                     if instanced and step is not None
                     else self.settle(asks, where, known))
            if declined(under):
                return under
            proof = self.seq(where, *sides, under, proof,
                        rules.DISCHARGE[(joins[i], first)])
        if stood_under:
            # An antecedent that is the scope is supplied by standing under
            # it, not by a fact looked up, so what it rests on is not carried
            # in by one: `readdcl` asks `( A ∈ ℝ ∧ B ∈ ℝ )`, the triangle
            # inequality's scope is exactly that, and its step 1 is the
            # lemma alone. It rests on everything the scope says.
            proof = Proof(proof.text,
                          proof.origin | self.scope_origin(where, known))
        return self.carry(proof, goal.rpn(self.flabel), frame)

    def at_its_own_value(self, label, sig, goal, scope, facts, step, settled):
        """A lemma proved at the value its own hypothesis gives it.

        `fsum1` concludes that a one-term sum is B and asks `( k = M -> A
        = B )`, which is not a condition on B but a statement of what B
        is. Taking B from the claim instead makes the hypothesis say
        something the claim's own words cannot prove: `G(0) = 1` asks that
        `a^k` be 1 at k = 0, which is `exp0` and wants a complex a, and a
        hypothesis with no antecedent has nothing to say about a.

        So the lemma proves what it does say — `G(0) = a^0` — and the
        claim is settled from that, here, where the theorem's `let a ∈ ℝ`
        is in scope. That is the only place the fact is available and the
        reason the closed hypothesis could never have carried it.
        """
        reads = self.syntax.statement(sig)
        while reads.label == 'wi':
            reads = reads.children[1]
        said = reads.substitute(settled)
        # Not a way back here: the match against `said` gives `settled`
        # back, and reading a hypothesis twice reads the same value.
        proof = self.apply_lemma(label, said, scope, facts, step,
                                 crossing=False)
        if declined(proof):
            return proof
        known = dict(facts)
        known[said.rpn(self.flabel)] = proof
        return self.settle(goal, scope, known)

    def prove_essential(self, want, scope, facts):
        """One hypothesis a lemma states in full rather than asking for."""
        if (want.label == 'wceq' and len(want.children) == 2
                and want.children[0].rpn(self.flabel)
                == want.children[1].rpn(self.flabel)):
            # A lemma that names a thing so that its conclusion may speak of
            # it asks for the naming, and asks for it as it stands rather
            # than under the scope: `ralrnmpt` wants `F = ( x e. A |-> B )`
            # of the very map F is. `settle` would carry it into the scope,
            # which is a deduction where the hypothesis is a statement.
            return self.seq(want.children[0].rpn(self.flabel), 'eqid')
        if want.label != 'wi':
            return self.settle(want, scope, facts)
        left, right = want.children
        under = left.rpn(self.flabel)
        if under == right.rpn(self.flabel):
            return self.seq(under, 'id')
        # A lemma may state its instance rather than ask for it: `elrab`
        # says what belongs to a set-builder by way of the body read at the
        # element, and wants the body before and after tied together.
        # `fsum1` does it with two terms where `elrab` does it with two
        # formulas, and the walk between them is the same walk.
        if (left.label == 'wceq' and right.label in ('wb', 'wceq')
                and left.children[0].label == 'cv'):
            was = left.children[0].rpn(self.flabel)
            now = left.children[1].rpn(self.flabel)
            return self.congruence(right.children[0], right.children[1],
                                   under, {under: self.seq(under, 'id')}, None,
                                   self.closing(('assumed', was, now, under)))
        if under == scope:
            return self.settle(right, scope, facts)
        if (left.label == 'wa'
                and left.children[0].rpn(self.flabel) == scope):
            extra = left.children[1].rpn(self.flabel)
            wider = {k: self.seq(under, scope, k, self.seq(scope, extra, 'simpl'), v,
                            'syl') for k, v in facts.items()}
            wider[extra] = self.seq(scope, extra, 'simpr')
            taken = self.at_the_index(left.children[1], right, under, wider)
            if taken is not None:
                return taken
            # One level deeper than `settle`'s default: what is asked of an
            # index is asked through the range it runs over, and the index
            # is in ℕ₀ only by `elfznn0` from that. `fsumdvds` asks the
            # digit sum's term d(k)·10^k − d(k) to be an integer, which is
            # `zsubcl`, `zmulcl`, `ffvelcdm` and then `elfznn0`.
            return self.settle(right, under, wider, depth=4)
        return self.settle(right, under, {})

    @staticmethod
    def conjuncts_of(slot):
        """The things a lemma's antecedent asks, one conjunct at a time."""
        pieces, parts = [], [slot]
        while parts:
            part = parts.pop(0)
            if part.label in ('wa', 'w3a'):
                parts[:0] = part.children
            else:
                pieces.append(part)
        return pieces

    def at_the_index(self, member, right, under, facts):
        """What a lemma asks of each index, from a line saying it of all.

        `fsumdvds` asks, for k in the range it sums over, that N divide the
        term, and the divisibility proof says it for every k ∈ ℕ₀. That is
        the line read at k, once k is in ℕ₀, which `rspcv` does. The line
        binds a letter of its own, since its `fix` introduced the index
        before the sum bound one, so what is compared is its body read at
        k. Only a line in hand whose body at k is what is asked is read so,
        which makes this an instantiation and not a search.

        None where no such line is in hand, which is not a decline: the
        caller settles what is asked another way.
        """
        if member.label != 'wcel' or member.children[0].label != 'cv':
            return None
        index = member.children[0]
        want = right.rpn(self.flabel)
        # Only what the step names, as `settle` is offered only that: a
        # line in scope and not cited is not there to be read.
        if self.resting is not None:
            facts = {k: v for k, v in facts.items()
                     if getattr(v, 'origin', frozenset()) <= self.resting}
        for said, proof in facts.items():
            line = self.to_term(said)
            if line.label != 'wral' or line.children[1].variable is None:
                continue
            body, letter, over = line.children
            if body.substitute({letter.variable: index.children[0]}).rpn(
                    self.flabel) != want:
                continue
            inside = self.seq(index.rpn(self.flabel), over.rpn(self.flabel),
                              'wcel')
            there = self.settle(self.to_term(inside), under, facts)
            if declined(there):
                continue
            reads = self.to_term(self.seq(
                self.seq(f'{letter.rpn(self.flabel)} cv',
                         index.rpn(self.flabel), 'wceq'),
                self.seq(body.rpn(self.flabel), want, 'wb'), 'wi'))
            tied = self.prove_essential(reads, under, facts)
            if declined(tied):
                continue
            read = self.ap('rspcv', {'ph': body.rpn(self.flabel), 'ps': want,
                                     'x': letter.rpn(self.flabel),
                                     'A': index.rpn(self.flabel),
                                     'B': over.rpn(self.flabel)}, tied)
            carried = self.seq(under, inside, self.seq(said, want, 'wi'),
                               there, read, 'syl')
            return self.seq(under, said, want, proof, carried, 'mpd')
        return None

    def one_direction(self, label, reads, goal, variables, scope, facts,
                      step, crossing, seed):
        """A claim `P → Q` from a lemma saying `Q ↔ P`, or `P ↔ Q`.

        The biconditional is proved at what the claim fixes, as the lemma
        states it, and the way the claim goes is taken: `biimpd` from left
        to right, `biimprd` from right to left.
        """
        left, right = reads.children
        for (first, then), fold in zip(((left, right), (right, left)),
                                       rules.ONE_WAY, strict=True):
            fixed = kernel.match(kernel.Term('wi', (first, then)), goal,
                                 dict(seed or {}), variables)
            if fixed is None:
                continue
            said = reads.substitute(fixed)
            both = self.apply_lemma(label, said, scope, facts, step,
                                    crossing, fixed)
            if declined(both):
                return both
            return self.seq(scope, left.substitute(fixed).rpn(self.flabel),
                            right.substitute(fixed).rpn(self.flabel), both,
                            fold)
        return Declined(f'neither way of {label} is the claim')
