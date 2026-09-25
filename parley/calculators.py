"""The calculators: `algebra`, `inequalities` and `arithmetic`.

This is the fifth of the elaborator's six parts (`ELABORATION.md`, "How the
elaborator is built"). Given a claim and the lines a step cites, each method
decides whether the claim follows and produces its proof; `METHODS.md`
specifies each. The deciding is done by `parley/field.py` (identities of the
field), `parley/linear.py` (linear facts over an ordered field) and
`parley/normal.py` (driving two terms to one canonical form, and the proof
that it did). What is here is how their answers become proof steps under the
step's scope.

What a method decides but cannot yet prove is taken as stated, and listed at
the head of the file it writes (`assume`, `stated`).
"""
from fractions import Fraction

import field
import linear
import normal
import rules
from library import Signature
from parse import Declined, declined, fmt
from provenance import REQUIRES
from scopes import Fact
from spell import seq


def order_sides(goal):
    """The two sides of a claim and which relation stands between them."""
    if goal.variable is not None:
        return None
    if goal.label == 'wceq' and len(goal.children) == 2:
        return goal.children[0], goal.children[1], '='
    if goal.label != 'wbr' or len(goal.children) != 3:
        return None
    how = {'cle': '<=', 'clt': '<'}.get(goal.children[2].label)
    return None if how is None else (goal.children[0], goal.children[1], how)


def whole_multiple(cited, claim):
    """How many times the claim the cited equation is, if a whole number.

    Both are the polynomial that must vanish, so one being a multiple of
    the other is the two saying the same thing at different scales.
    """
    if cited is None or claim is None or not claim.terms:
        return None
    lead = max(claim.terms)
    if lead not in cited.terms:
        return None
    times = cited.terms[lead] / claim.terms[lead]
    if times.denominator != 1 or not 2 <= times.numerator <= 9:
        return None
    if cited.terms != claim.scaled(times).terms:
        return None
    return times.numerator


def multiplier(shape, scale):
    """The term a combination multiplies one cited equation by, or None.

    `field.spell` writes the canonical polynomial, which raises an atom to
    the first power and multiplies it by one. That is what two polynomials
    being compared want and not what a factor wants: `( -u 1 x. ( q ^ 1 ) )`
    asks for two memberships nothing declares where `-u q` asks for one that
    is. So a multiplier is written the short way.
    """
    monomials = list(shape.terms)
    if len(monomials) != 1 or shape.terms[monomials[0]] != 1:
        return None
    parts = monomials[0]
    if not parts:
        return field.spell_coefficient(scale)
    if len(parts) != 1 or parts[0][1] != 1:
        return None
    name = parts[0][0]
    if scale == 1:
        return name
    if scale == -1:
        return seq(name, 'cneg')
    digit = field.spell_coefficient(scale)
    return None if digit is None else seq(digit, name, 'cmul', 'co')


def rescales(cited, claim):
    """What the cited polynomial is multiplied by to become the claim's.

    Two disequalities say one thing when one polynomial is the other
    scaled: `1 − a` is `−1` times `a − 1`, so `1 − a ≠ 0` and `a ≠ 1` deny
    the same number. Any nonzero rational will do, where `whole_multiple`
    wants a digit, because nothing here has to spell the scalar.
    """
    if cited is None or claim is None or not cited.terms or not claim.terms:
        return None
    lead = max(claim.terms)
    if lead not in cited.terms:
        return None
    times = claim.terms[lead] / cited.terms[lead]
    if times == 0 or claim.terms != cited.scaled(times).terms:
        return None
    return times


class Calculators:
    def algebra(self, step, node, term, scope, facts, lines):
        """Decided by `parley/field.py`, then proved by `parley/normal.py`.

        A step that is not an identity of the field is refused rather than
        assumed. One that is gets a proof where `normal.py` can build one:
        both sides are driven to the same canonical term and the step is
        the two of them meeting. What that module does not yet write — a
        quotient, a coefficient past one digit — is taken as stated, which
        is what every `algebra` step was before it existed.
        """
        self.decide_field(step, term, lines)
        found = self.prove_field(step, term, scope, facts, lines)
        if declined(found):
            return self.assume(step, term, scope, facts, 'alg', lines)
        return found

    def prove_field(self, step, term, scope, facts, lines):
        """An `algebra` claim, by whichever of two routes reaches it."""
        goal = self.to_term(term)
        apart = (goal.variable is None and goal.label == 'wn'
                 and len(goal.children) == 1)
        if not apart and (goal.variable is not None or goal.label != 'wceq'
                          or len(goal.children) != 2):
            return Declined('the claim is not an equation')

        self.combining(term)
        # A `requires` line is where a step says its denominator is not
        # zero, so what the normalizer is asked is asked of those as well
        # as of the scope.
        facts = self.supplied(step, scope, facts) if step is not None \
            else facts

        def complex_number(said):
            """What `normal.py` asks of a subterm it does not look inside."""
            return self.membership(said, 'cc', scope, facts)

        work = normal.Emitter(self.sigs, scope, complex_number,
                              self.not_zero(scope, facts))
        if apart:
            return self.apart_from_cited(step, goal, scope, facts, lines,
                                         work, complex_number)
        left = goal.children[0].rpn(self.flabel)
        right = goal.children[1].rpn(self.flabel)
        # The routes, in the order they cost, and what each said when it
        # declined. Nested `try`s kept only the last of those, so the step
        # was refused in the words of whichever route happened to be tried
        # last rather than of the one that came nearest.
        routes = [lambda: self.same_polynomial(work, left, right)]
        if step is not None:
            routes += [
                lambda: self.scaled_from_cited(step, left, right, scope,
                                               facts, lines, work),
                lambda: self.crossed_from_cited(step, left, right, scope,
                                                facts, lines, work),
                lambda: self.summed_from_cited(step, left, right, scope,
                                               facts, lines, work)]
        declines = []
        for route in routes:
            found = route()
            if not declined(found):
                return found
            declines.append(str(found))
        return Declined('; '.join(declines))

    def apart_from_cited(self, step, goal, scope, facts, lines, work,
                         complex_number):
        """A disequality that is a cited one rescaled.

        What the claim says does not vanish is what a cited disequality says
        does not vanish, scaled. So the cited fact becomes a difference that
        is not zero, the two differences are shown to be one polynomial, and
        the claim's difference is not zero either. `subeq0` is what carries a
        difference being zero to the two sides being equal, in both
        directions and under both negations.

        The scalar is 1 or −1. `decide_field` allows any nonzero rational and
        a step wanting another is refused here rather than guessed at: it
        would have to be spelt as a term and multiplied in, and the corpus
        has no such step to check that against.
        """
        if step is None:
            return Declined('a disequality needs the step it cites')
        claim = field.denied(goal, self.flabel)
        left, right = goal.children[0].children
        lhs, rhs = left.rpn(self.flabel), right.rpn(self.flabel)
        whole = self.seq(lhs, rhs, 'cmin', 'co')
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                node = self.to_term(said)
                cited = field.denied(node, self.flabel)
                if cited is None or rescales(cited, claim) not in (1, -1):
                    continue
                p, q = (c.rpn(self.flabel)
                        for c in node.children[0].children)
                gap = self.seq(p, q, 'cmin', 'co')
                given = self.cited_fact(ref, node, scope, facts, lines)
                if declined(given):
                    return given
                apart = work.ap(
                    'subne0d', {'ph': scope, 'A': p, 'B': q},
                    complex_number(p), complex_number(q),
                    work.ap('neqned', {'ph': scope, 'A': p, 'B': q}, given))
                if rescales(cited, claim) == -1:
                    apart = work.ap('negne0d', {'ph': scope, 'A': gap},
                                    complex_number(gap), apart)
                    gap = self.seq(gap, 'cneg')
                alike = self.same_polynomial(work, gap, whole)
                if declined(alike):
                    return alike
                return work.ap(
                    'neneqd', {'ph': scope, 'A': lhs, 'B': rhs},
                    work.ap(
                        'subne0ad', {'ph': scope, 'A': lhs, 'B': rhs},
                        complex_number(lhs), complex_number(rhs),
                        work.ap('eqnetrrd',
                                {'ph': scope, 'A': gap, 'B': whole,
                                 'C': 'cc0'},
                                alike, apart)))
        return Declined('no cited disequality is the claim rescaled')

    def crossed_from_cited(self, step, left, right, scope, facts, lines,
                           work):
        """A claim the cited equation already is, once its division goes.

        sqrt2-irrational concludes `m^2 = 2 j^2` from `( m / j ) ^ 2 = 2`.
        Those are the same equation: the second divides where the first
        has multiplied out, and `divmuleq` is the step between them.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
                              self.flabel)
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            cited = self.to_term(held.term)
            if cited.variable is not None or cited.label != 'wceq' \
                    or len(cited.children) != 2:
                continue
            mine = field.equation(cited, self.flabel)
            if want is None or mine is None or mine.terms != want.terms:
                continue
            given = self.cited_fact(ref, cited, scope, facts, lines)
            if declined(given):
                continue
            found = self.cleared(work, cited, left, right, given)
            if not declined(found):
                return found
        return Declined('no cited equation is the claim divided')

    def cleared(self, work, cited, left, right, given):
        """The cited equation with its denominators multiplied out."""
        was = [one.rpn(self.flabel) for one in cited.children]
        quotients = []
        for side, said in zip(cited.children, was, strict=True):
            made = work.normalize_quotient(side, self.flabel)
            if declined(made):
                return made
            quotients.append(work.as_quotient(*made, said))
        (over, under, first), (below, beneath, second) = quotients
        a, b = work.spell_run(over), work.spell_run(under)
        c, d = work.spell_run(below), work.spell_run(beneath)
        pairs = [work.pair_of(under), work.pair_of(beneath)]
        for one in pairs:
            if declined(one):
                return one
        crossed = work.ap(
            'mpbid', {'ph': work.under,
                      'ps': self.seq(self.seq(a, b, 'cdiv', 'co'),
                                self.seq(c, d, 'cdiv', 'co'), 'wceq'),
                      'ch': self.seq(self.seq(a, d, 'cmul', 'co'),
                                self.seq(c, b, 'cmul', 'co'), 'wceq')},
            work.ap('3eqtr3d', {'ph': work.under, 'A': was[0], 'B': was[1],
                                'C': self.seq(a, b, 'cdiv', 'co'),
                                'D': self.seq(c, d, 'cdiv', 'co')},
                    given, first, second),
            work.ap('syl2anc',
                    {'ph': work.under,
                     'ps': seq(seq(a, 'cc', 'wcel'), seq(c, 'cc', 'wcel'),
                               'wa'),
                     'ch': seq(seq(seq(b, 'cc', 'wcel'),
                                   seq(b, 'cc0', 'wne'), 'wa'),
                               self.seq(self.seq(d, 'cc', 'wcel'),
                                   self.seq(d, 'cc0', 'wne'), 'wa'), 'wa'),
                     'th': self.seq(self.seq(self.seq(a, b, 'cdiv', 'co'),
                                   self.seq(c, d, 'cdiv', 'co'), 'wceq'),
                               self.seq(self.seq(a, d, 'cmul', 'co'),
                                   self.seq(c, b, 'cmul', 'co'), 'wceq'), 'wb')},
                    work.ap('jca', {'ph': work.under,
                                    'ps': self.seq(a, 'cc', 'wcel'),
                                    'ch': self.seq(c, 'cc', 'wcel')},
                            work.run_cc(over), work.run_cc(below)),
                    work.ap('jca', {'ph': work.under,
                                    'ps': self.seq(self.seq(b, 'cc', 'wcel'),
                                              self.seq(b, 'cc0', 'wne'), 'wa'),
                                    'ch': self.seq(self.seq(d, 'cc', 'wcel'),
                                              self.seq(d, 'cc0', 'wne'), 'wa')},
                            *pairs),
                    work.ap('divmuleq', {'A': a, 'B': c, 'C': b, 'D': d})))
        sides = [self.same_polynomial(work, left, self.seq(a, d, 'cmul', 'co')),
                 self.same_polynomial(work, right, self.seq(c, b, 'cmul', 'co'))]
        for one in sides:
            if declined(one):
                return one
        return work.ap(
            '3eqtr4d', {'ph': work.under, 'A': self.seq(a, d, 'cmul', 'co'),
                        'B': self.seq(c, b, 'cmul', 'co'), 'C': left,
                        'D': right},
            crossed, *sides)

    def not_zero(self, scope, facts):
        """What says a denominator is not zero, asked of the scope.

        The text writes these: `requires 2 =/= 0` and `requires q =/= 0`
        are what a step dividing by either of them carries, so the fact is
        there to be found rather than to be proved again here.
        """
        def apart(said):
            want = self.seq(said, 'cc0', 'wne')
            if want in facts:
                return facts[want]
            denied = self.seq(self.seq(said, 'cc0', 'wceq'), 'wn')
            if denied in facts:
                return self.seq(scope, said, 'cc0', facts[denied], 'neqned')
            found = self.apart_as_written(said, scope, facts)
            if found is not None:
                return found
            # `normal.py` asks this while writing a proof it has already
            # decided, and takes what it is given. A decline handed back
            # there reaches the step as the method not covering it, which
            # is not what a missing `requires` line means.
            settled = self.settle(self.to_term(want), scope, facts)
            if declined(settled):
                raise self.defect(
                    self.at, f'nothing says {self.render(want)}, which this '
                             f'step needs to divide by it')
            return settled
        return apart

    def apart_as_written(self, said, scope, facts):
        """The same fact about the same denominator, spelt as the text spells it.

        A step writes `1 − a ≠ 0` and the normalizer asks about the
        polynomial that is, which it writes as −1·a¹ + 1·1. Those are one
        number and the two lookups above compare spellings, so the fact the
        step wrote is there and is missed. What decides is the polynomial,
        and the equation carrying one spelling to the other is the
        normalizer's own: it is what `normalize` returns beside the terms.
        """
        work = normal.Emitter(
            self.sigs, scope,
            lambda term: self.membership(term, 'cc', scope, facts))
        for fact, proof in facts.items():
            tail = fact.split()[-1]
            if tail not in ('wne', 'wn'):
                continue
            node = self.to_term(fact)
            if node.variable is not None:
                continue
            if node.label == 'wn':
                inner = node.children[0]
                if inner.variable is not None or inner.label != 'wceq':
                    continue
                subject, zero = inner.children
                given = self.seq(scope, subject.rpn(self.flabel), 'cc0', proof,
                            'neqned')
            else:
                subject, zero = node.children
                given = proof
            was = subject.rpn(self.flabel)
            if zero.rpn(self.flabel) != 'cc0' or was == said:
                continue
            made = work.normalize(subject, self.flabel)
            if declined(made):
                continue
            items, same = made
            if work.spell_run(items) != said:
                continue
            return work.ap('eqnetrrd',
                           {'ph': scope, 'A': was, 'B': said, 'C': 'cc0'},
                           same, given)
        return None

    def same_polynomial(self, work, left, right):
        """Two terms driven to one canonical form, and so to each other.

        Where either divides, the canonical form is a numerator over a
        denominator, and two of those are the same when the cross product
        of them is — which is `divmuleq`, and leaves a polynomial identity
        for the case above to answer.
        """
        made = work.normalize_quotient(self.to_term(left), self.flabel)
        if declined(made):
            return made
        first_items, first_under, first = made
        made = work.normalize_quotient(self.to_term(right), self.flabel)
        if declined(made):
            return made
        second_items, second_under, second = made
        if first_under is None and second_under is None:
            if work.spell_run(first_items) != work.spell_run(second_items):
                return Declined('the two are not one polynomial')
            return work.ap('eqtr4d',
                           {'ph': work.under, 'A': left,
                            'B': work.spell_run(first_items), 'C': right},
                           first, second)
        return self.cross_multiplied(work, left, right,
                                     first_items, first_under, first,
                                     second_items, second_under, second)

    def cross_multiplied(self, work, left, right, over, under, first,
                         below, beneath, second):
        """Two quotients equal, because their cross product is."""
        over, under, first = work.as_quotient(over, under, first, left)
        below, beneath, second = work.as_quotient(below, beneath, second,
                                                  right)
        a, b = work.spell_run(over), work.spell_run(under)
        c, d = work.spell_run(below), work.spell_run(beneath)
        crossed = self.same_polynomial(work, self.seq(a, d, 'cmul', 'co'),
                                       self.seq(c, b, 'cmul', 'co'))
        if declined(crossed):
            return crossed
        pairs = [work.pair_of(beneath), work.pair_of(under)]
        for one in pairs:
            if declined(one):
                return one
        return work.ap(
            'eqtr4d', {'ph': work.under, 'A': left,
                       'B': self.seq(a, b, 'cdiv', 'co'), 'C': right},
            first,
            work.ap('eqtrd', {'ph': work.under, 'A': right,
                              'B': self.seq(c, d, 'cdiv', 'co'),
                              'C': self.seq(a, b, 'cdiv', 'co')},
                    second,
                    work.ap('mpbird',
                            {'ph': work.under,
                             'ps': self.seq(self.seq(c, d, 'cdiv', 'co'),
                                       self.seq(a, b, 'cdiv', 'co'), 'wceq'),
                             'ch': self.seq(self.seq(c, b, 'cmul', 'co'),
                                       self.seq(a, d, 'cmul', 'co'), 'wceq')},
                            work.ap('eqcomd',
                                    {'ph': work.under,
                                     'A': self.seq(a, d, 'cmul', 'co'),
                                     'B': self.seq(c, b, 'cmul', 'co')}, crossed),
                            work.ap('syl2anc',
                                    {'ph': work.under,
                                     'ps': self.seq(self.seq(c, 'cc', 'wcel'),
                                               self.seq(a, 'cc', 'wcel'), 'wa'),
                                     'ch': self.seq(self.seq(self.seq(d, 'cc', 'wcel'),
                                                   self.seq(d, 'cc0', 'wne'),
                                                   'wa'),
                                               self.seq(self.seq(b, 'cc', 'wcel'),
                                                   self.seq(b, 'cc0', 'wne'),
                                                   'wa'), 'wa'),
                                     'th': seq(seq(seq(c, d, 'cdiv', 'co'),
                                                   seq(a, b, 'cdiv', 'co'),
                                                   'wceq'),
                                               seq(seq(c, b, 'cmul', 'co'),
                                                   seq(a, d, 'cmul', 'co'),
                                                   'wceq'), 'wb')},
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': self.seq(c, 'cc', 'wcel'),
                                             'ch': self.seq(a, 'cc', 'wcel')},
                                            work.run_cc(below),
                                            work.run_cc(over)),
                                    work.ap('jca',
                                            {'ph': work.under,
                                             'ps': self.seq(self.seq(d, 'cc', 'wcel'),
                                                       self.seq(d, 'cc0', 'wne'),
                                                       'wa'),
                                             'ch': self.seq(self.seq(b, 'cc', 'wcel'),
                                                       self.seq(b, 'cc0', 'wne'),
                                                       'wa')},
                                            *pairs),
                                    work.ap('divmuleq',
                                            {'A': c, 'B': a, 'C': d,
                                             'D': b})))))

    def summed_from_cited(self, step, left, right, scope, facts, lines, work):
        """A claim the cited equations add up to.

        Bezout's step 3 takes three at once — `c = q·d + r`, `c = a·u + b·v`
        and `d = a·x₀ + b·y₀` — at −1, 1 and −q, and is the only step in the
        corpus whose multipliers are not all constants. `decide_field` works
        those out to decide the step at all and hands them over; what is
        left is saying it. Each cited equation is a difference that is zero;
        each is multiplied by what the combination says, and stays zero; the
        sum of them is zero because every one is; and that sum is the
        claim's own difference, which is the normalizer's question.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
                              self.flabel)
        given, where = [], []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                node = self.to_term(said)
                one = field.equation(node, self.flabel)
                if one is not None:
                    given.append(one)
                    where.append((ref, node))
        if want is None or not given:
            return Declined('the step cites no equation')

        def in_cc(said):
            """( scope -> said e. CC ), for a term of the step's own depth.

            The claim's sides are as deep as the step wrote them — Bezout's
            is a sum of two products of a difference of a product — and each
            level is a closure lemma with the atoms at the bottom reached
            through `recn`. Five is not enough for that and is the depth a
            side condition wants, so this asks for its own.

            Built by `part` first, which is that walk done by table with the
            atoms taken from the step's own lines. Searched for, `zcn` stands
            before `mulcl`, and the product came from the hypotheses through
            ℤ while the lines the step wrote for its atoms went unused.
            """
            found = self.part(said, 'cc', scope, facts)
            if not declined(found):
                return found
            return self.settle(self.to_term(self.seq(said, 'cc', 'wcel')), scope,
                               facts, depth=12)

        atoms = {a for p in [*given, want] for m in p.terms for a, _ in m}
        how = field.follows(given, want, atoms)
        if not how:
            return Declined('no sum of the cited equations is the '
                                   'claim')
        self.combining(self.seq(left, right, 'wceq'),
                       *(where[which][1].rpn(self.flabel)
                         for which, _shape, _scale in how))
        pieces = []
        for which, shape, scale in how:
            ref, node = where[which]
            a, b = (c.rpn(self.flabel) for c in node.children)
            gap = self.seq(a, b, 'cmin', 'co')
            times = multiplier(shape, scale)
            if times is None:
                return Declined('a multiplier with no spelling')
            parts = [self.cited_fact(ref, node, scope, facts, lines),
                     in_cc(a), in_cc(b)]
            for one in parts:
                if declined(one):
                    return one
            given, a_cc, b_cc = parts
            vanishes = work.ap(
                'mpbird', {'ph': scope, 'ps': self.seq(gap, 'cc0', 'wceq'),
                           'ch': self.seq(a, b, 'wceq')},
                given,
                work.ap('subeq0ad', {'ph': scope, 'A': a, 'B': b},
                        a_cc, b_cc))
            piece = self.seq(times, gap, 'cmul', 'co')
            pieces.append((piece, work.ap(
                'eqtrd', {'ph': scope, 'A': piece,
                          'B': self.seq(times, 'cc0', 'cmul', 'co'), 'C': 'cc0'},
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': times, 'F': 'cmul'}, vanishes),
                work.ap('mul01d', {'ph': scope, 'A': times},
                        work.atom(times)))))
        total, sums = pieces[0]
        for piece, proof in pieces[1:]:
            joined = self.seq(total, piece, 'caddc', 'co')
            sums = work.ap(
                'eqtrd', {'ph': scope, 'A': joined,
                          'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0'},
                work.ap('oveq12d',
                        {'ph': scope, 'A': total, 'B': 'cc0', 'C': piece,
                         'D': 'cc0', 'F': 'caddc'}, sums, proof),
                work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0',
                             'wceq'), '00id'))
            total = joined
        whole = self.seq(left, right, 'cmin', 'co')
        ends = [self.same_polynomial(work, total, whole),
                in_cc(left), in_cc(right)]
        for one in ends:
            if declined(one):
                return one
        alike, left_cc, right_cc = ends
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(whole, 'cc0', 'wceq'),
                      'ch': self.seq(left, right, 'wceq')},
            work.ap('eqtr3d',
                    {'ph': scope, 'A': total, 'B': whole, 'C': 'cc0'},
                    alike, sums),
            work.ap('subeq0ad', {'ph': scope, 'A': left, 'B': right},
                    left_cc, right_cc))

    def scaled_from_cited(self, step, left, right, scope, facts, lines, work):
        """A claim a cited equation is a whole multiple of.

        sqrt2-irrational concludes `j^2 = 2 p^2` from `2 j^2 = 4 p^2`: the
        equation it cites is the claim with both sides doubled. Proving
        each side is that multiple is the polynomial case again, and what
        is left is cancelling the multiplier.
        """
        want = field.equation(self.to_term(self.seq(left, right, 'wceq')),
                              self.flabel)
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            cited = self.to_term(held.term)
            if cited.variable is not None or cited.label != 'wceq':
                continue
            times = whole_multiple(
                field.equation(cited, self.flabel), want)
            if times is None or f'{times}ne0' not in self.sigs:
                continue
            scaled = [self.seq(field.NUMERAL[times], one, 'cmul', 'co')
                      for one in (left, right)]
            sides = [self.same_polynomial(work, was, now) for was, now
                     in zip([c.rpn(self.flabel) for c in cited.children],
                            scaled, strict=True)]
            if any(declined(one) for one in sides):
                continue
            self.combining(self.seq(left, right, 'wceq'), held.term)
            return self.cancel_multiple(work, times, left, right, scaled,
                                        sides, self.carried(ref, facts,
                                                            lines),
                                        cited, scope, facts)
        return Declined('no cited equation is a multiple of the claim')

    def cancel_multiple(self, work, times, left, right, scaled, sides,
                        given, cited, scope, facts):
        """The multiplier taken off both sides, which is `mulcan`."""
        numeral = field.NUMERAL[times]
        matched = work.ap(
            '3eqtr3d', {'ph': scope, 'A': cited.children[0].rpn(self.flabel),
                        'B': cited.children[1].rpn(self.flabel),
                        'C': scaled[0], 'D': scaled[1]},
            given, *sides)
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(scaled[0], scaled[1], 'wceq'),
                      'ch': self.seq(left, right, 'wceq')},
            matched,
            work.ap('syl3anc',
                    {'ph': scope, 'ps': self.seq(left, 'cc', 'wcel'),
                     'ch': self.seq(right, 'cc', 'wcel'),
                     'th': self.seq(self.seq(numeral, 'cc', 'wcel'),
                               self.seq(numeral, 'cc0', 'wne'), 'wa'),
                     'ta': self.seq(self.seq(scaled[0], scaled[1], 'wceq'),
                               self.seq(left, right, 'wceq'), 'wb')},
                    self.membership(left, 'cc', scope, facts),
                    self.membership(right, 'cc', scope, facts),
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(numeral, 'cc', 'wcel'),
                                    'ch': self.seq(numeral, 'cc0', 'wne')},
                            work.number(times),
                            work.a1i(self.seq(numeral, 'cc0', 'wne'),
                                     f'{times}ne0')),
                    work.ap('mulcan', {'A': left, 'B': right,
                                       'C': numeral})))

    def decide_field(self, step, term, lines):
        """Refuse an `algebra` step that is not an identity.

        With nothing cited the claim must vanish outright; with equations
        cited it must be a combination of them. That the denominators are
        not zero is not decided here — the text writes those as `requires`
        lines, which is what `METHODS.md` means by them being hypotheses of
        the method.
        """
        claim = field.equation(self.to_term(term), self.flabel)
        if claim is None:
            return self.decide_apart(step, term, lines)
        given = []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = field.equation(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
        atoms = {a for p in [*given, claim] for m in p.terms for a, _ in m}
        if field.follows(given, claim, atoms) is None:
            raise self.defect(step.line,
                              f'{self.render(term)} is not an identity, nor '
                              f'does it follow from what step '
                              f'{fmt(step.number)} cites')

    def decide_apart(self, step, term, lines):
        """Refuse a disequality `algebra` step that is not a cited one rescaled.

        This method is allowed one disequality and no more: the claim holds
        when what it says does not vanish is a nonzero multiple of what a
        cited disequality says does not vanish. Anything else is a fact
        about the field rather than an identity of it — that a² is not zero
        when a is not needs the field to have no zero divisors, and nothing
        here decides that.

        A claim that is neither an equation nor a disequality is left alone,
        as it was before either was decided.
        """
        claim = field.denied(self.to_term(term), self.flabel)
        if claim is None:
            return
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = field.denied(self.to_term(said), self.flabel)
                if one is not None and rescales(one, claim) is not None:
                    return
        raise self.defect(step.line,
                          f'{self.render(term)} is not a rescaling of any '
                          f'disequality step {fmt(step.number)} cites')

    def arithmetic(self, step, node, term, scope, facts, lines):
        """Closed numerals, worked out and then said. `METHODS.md`.

        A relation between two numerals is said outright; a value is an
        identity of the field with no atoms in it, so it goes where
        identities go rather than wanting a second procedure.

        Nothing is taken as stated. The claim is worked out first
        (`field.decide_closed`), so what cannot be proved is reported as
        what it is: false, or not a number, or true and past what the
        method can show, which a theorem stating it is cited for.
        """
        what = f'step {fmt(step.number)} claims {" ".join(step.claim)}'
        return self.closed_fact(term, scope, facts, what, step)

    def closed_fact(self, term, scope, facts, what, step=None):
        """A fact about closed numerals, worked out and then proved.

        Wherever it stands: a step of its own, the equation a `substitute`
        rewrites by, or a link of a `calculation`. A claim with nothing in
        it but numerals gives a reader nothing to check but working it out,
        so the page may name `arithmetic` where the fact is used, and each
        of those places is held to the same refusals as a step. `what` says
        where it was asked, as the page writes it.
        """
        self.worked_out(term, what)
        for how in (lambda: self.prove_numeral(term, scope, facts),
                    lambda: self.prove_field(step, term, scope, facts, {})):
            found = how()
            if not declined(found):
                return found
        raise self.unshown(term, what)

    def worked_out(self, term, what):
        """A claim `arithmetic` is asked for, refused where it is false or
        has no exact value. `what` says where it was asked, as the page
        writes it.
        """
        verdict = field.decide_closed(self.to_term(term), self.flabel)
        if declined(verdict):
            return
        if verdict.holds is False:
            raise self.defect(self.at, f'{what}, which is false')
        if verdict.holds is None:
            raise self.defect(self.at, f'{what}, which {verdict.reason}')

    def unshown(self, term, what):
        """The defect for a claim `arithmetic` could not prove.

        It is never taken as stated instead: a numeral fact the method
        cannot show is cited from a theorem that states it, as the
        divisibility proof cites 10 − 1 = 9.
        """
        verdict = field.decide_closed(self.to_term(term), self.flabel)
        if declined(verdict):
            return self.defect(self.at, f'{what}, which is not a fact about '
                                        f'numerals alone, and arithmetic '
                                        f'decides nothing else')
        return self.defect(self.at, f'{what}, which is true, and arithmetic '
                                    f'cannot show it yet; cite a theorem '
                                    f'that states it')

    def prove_numeral(self, term, scope, facts):
        """A closed numeral fact, decided by working it out and then said.

        What `arithmetic` takes is closed, so deciding is arithmetic on two
        whole numbers and needs no procedure. Saying it rests on one thing
        set.mm names for every pair — that one number is below another —
        and everything else is that weakened or turned: `ltle` for `at
        most`, `ltne` for `not equal`, `leid` and `eqid` where the two are
        the same number.
        """
        goal = self.to_term(term)
        negated = False
        if goal.variable is None and goal.label == 'wn' \
                and len(goal.children) == 1:
            negated, goal = True, goal.children[0]
        # Belonging to a number system is the other thing a claim with no
        # atom can say, and `METHODS.md` puts every such claim under this
        # method, so a line saying `arithmetic` for `2 e. ZZ` is decided here
        # rather than by whatever `rules.MEMBERSHIP` reaches.
        if not negated and goal.variable is None and goal.label == 'wcel' \
                and len(goal.children) == 2:
            return self.numeral_within(goal, scope, facts)
        sides = order_sides(goal)
        if sides is None:
            return Declined('the claim states no relation')
        first, second = (linear.numeral(one, self.flabel)
                         for one in sides[:2])
        if first is None or second is None \
                or first.denominator != 1 or second.denominator != 1 \
                or not all(0 <= int(n) <= 9 for n in (first, second)):
            return Declined('the two sides are not single digits')
        # Each side must *be* its digit, not merely come to it. What set.mm
        # names is a fact about the digits, so a side that works out to one
        # without being written as one is a computation, and this is not
        # the method that does computations.
        if any(one.rpn(self.flabel) != field.NUMERAL[int(value)]
               for one, value in zip(sides[:2], (first, second),
                                     strict=True)):
            return Declined('a side works out to a digit but is one '
                                   'only after working out')
        a, b, how = int(first), int(second), sides[2]
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        if negated:
            if how != '=' or a == b:
                return Declined('a denial of what holds')
            return self.numerals_differ(work, a, b)
        if how == '=' and a == b:
            return work.a1i(self.seq(field.NUMERAL[a], field.NUMERAL[b], 'wceq'),
                            work.ap('eqid', {'A': field.NUMERAL[a]}))
        if how == '<' and a < b:
            return self.numeral_below(work, a, b)
        if how == '<=' and a <= b:
            if a == b:
                return work.ap(
                    'syl', {'ph': scope,
                            'ps': self.seq(field.NUMERAL[a], 'cr', 'wcel'),
                            'ch': self.seq(field.NUMERAL[a], field.NUMERAL[a],
                                      'cle', 'wbr')},
                    self.numeral_real(work, a),
                    work.ap('leid', {'A': field.NUMERAL[a]}))
            return work.ap(
                'mpd', {'ph': scope,
                        'ps': self.seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                                  'wbr'),
                        'ch': self.seq(field.NUMERAL[a], field.NUMERAL[b], 'cle',
                                  'wbr')},
                self.numeral_below(work, a, b),
                work.ap('syl2anc',
                        {'ph': scope,
                         'ps': self.seq(field.NUMERAL[a], 'cr', 'wcel'),
                         'ch': self.seq(field.NUMERAL[b], 'cr', 'wcel'),
                         'th': self.seq(self.seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'clt', 'wbr'),
                                   self.seq(field.NUMERAL[a], field.NUMERAL[b],
                                       'cle', 'wbr'), 'wi')},
                        self.numeral_real(work, a),
                        self.numeral_real(work, b),
                        work.ap('ltle', {'A': field.NUMERAL[a],
                                         'B': field.NUMERAL[b]})))
        return Declined(f'{a} {how} {b} is not what the numbers do')

    def numeral_real(self, work, value):
        return work.a1i(self.seq(field.NUMERAL[value], 'cr', 'wcel'),
                        f'{value}re')

    def numeral_below(self, work, a, b):
        """( scope -> a < b ), the one thing set.mm names for every pair.

        It names `0 < n` as `npos` rather than `0ltn`, and one is the
        exception to that, so the three spellings are all there is.
        """
        if a != 0:
            label = f'{a}lt{b}'
        else:
            label = '0lt1' if b == 1 else f'{b}pos'
        return work.a1i(self.seq(field.NUMERAL[a], field.NUMERAL[b], 'clt',
                            'wbr'), label)

    def numerals_differ(self, work, a, b):
        """( scope -> -. a = b ), from whichever of the two is below."""
        low, high = (a, b) if a < b else (b, a)
        apart = work.ap(
            'syl', {'ph': work.under,
                    'ps': self.seq(self.seq(field.NUMERAL[low], 'cr', 'wcel'),
                              self.seq(field.NUMERAL[low], field.NUMERAL[high],
                                  'clt', 'wbr'), 'wa'),
                    'ch': self.seq(field.NUMERAL[high], field.NUMERAL[low],
                              'wne')},
            work.ap('jca', {'ph': work.under,
                            'ps': self.seq(field.NUMERAL[low], 'cr', 'wcel'),
                            'ch': self.seq(field.NUMERAL[low],
                                      field.NUMERAL[high], 'clt', 'wbr')},
                    self.numeral_real(work, low),
                    self.numeral_below(work, low, high)),
            work.ap('ltne', {'A': field.NUMERAL[low],
                             'B': field.NUMERAL[high]}))
        if a != low:
            return work.ap('neneqd', {'ph': work.under,
                                      'A': field.NUMERAL[a],
                                      'B': field.NUMERAL[b]}, apart)
        return work.ap(
            'neneqd', {'ph': work.under, 'A': field.NUMERAL[a],
                       'B': field.NUMERAL[b]},
            work.ap('necomd', {'ph': work.under, 'A': field.NUMERAL[high],
                               'B': field.NUMERAL[low]}, apart))

    def inequalities(self, step, node, term, scope, facts, lines):
        """Decided by `parley/linear.py`, and then taken.

        The decision is not the proof. What the method concludes is checked
        against what the step cites — the claim is denied and the set shown
        to have no solution over an ordered field — so a step that does not
        follow is refused rather than assumed. What is still assumed is the
        step it was allowed to take, which is why the head of the file
        lists it. Emitting the proof of a decided step wants a normal form
        for sums that `algebra` does not have yet.

        A step that cites nothing decidable is taken as before: the method
        carries steps whose facts are not linear, and `METHODS.md` refuses
        those rather than this.
        """
        self.decide_order(step, term, lines)
        # The method wants every atom in ℝ, and a `requires` line is where
        # the step writes that. Reading them here is what puts the page's
        # justification in the proof: settled instead, the membership comes
        # from whatever `rules.MEMBERSHIP` reaches, which is the table for
        # what the readable layer does not write.
        known = self.supplied(step, scope, facts) if step is not None \
            else facts
        # Offered to the membership lookup and to nothing else. `settle`
        # searches what it is given, and widening the facts it sees widens
        # that search: handing `prove_order` the whole of `known` put the
        # four steps of `thm:proof/triangle-inequality/abs-bounds` past ten
        # million `fits` calls, where the same proof takes five seconds.
        # What a requires line made, and nothing else — including where the
        # scope holds the same claim for another reason, which is the case
        # the line was written for: `requires x ∈ ℝ: from H1` beside the
        # hypothesis that says it.
        kept = self.written
        self.written = {k: (scope, v) for k, v in known.items()
                        if any(o.startswith(REQUIRES)
                               for o in getattr(v, 'origin', ()))}
        try:
            found = self.prove_order(step.just.refs, term, scope, facts,
                                     lines)
        finally:
            self.written = kept
        if declined(found):
            return self.assume(step, term, scope, facts, 'ine', lines)
        return found

    def prove_order(self, refs, term, scope, facts, lines, skip=()):
        """An `inequalities` claim, by whichever route reaches it.

        `skip` names sentences of the cited lines to leave out. A case of a
        split is proved by this same method one scope in, and the
        disequality it split on must not be there to split on again.

        What is passed is the lines the claim rests on, not the step, so
        that a `requires` line asking for the method is answered the same
        way a step is: `side` has citations where a step has `from`.

        `linear.certificate` says which cited facts the claim is built
        from and in what multiple. Where the only one used is an equation,
        the claim is that equation times a number: the difference it says
        is zero, scaled, is the difference the claim says is zero, and the
        two being the same expression is a question for the normalizer.

        Otherwise the claim is the cited bounds added (`from_sum`), keeping
        a strict one strict (`strictly`). A combination of more than two
        bounds, or one scaling a bound by other than one, is not written,
        and a step needing one is stated.
        """
        goal = self.to_term(term)
        given, where = [], []
        for ref in refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                if said in skip:
                    continue
                one = linear.fact(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
                    where.append((ref, self.to_term(said)))
        claim = linear.fact(goal, self.flabel)
        if claim is None:
            return Declined('the claim is not linear')
        self.combining(term)
        closed = self.by_antisymmetry(goal, scope, facts)
        if closed is not None:
            return closed
        found = linear.certificate([*given, linear.opposite(claim)])
        if not isinstance(found, dict):
            return self.either_way(found, refs, where, given, term, scope,
                                   facts, lines, skip)
        if len(given) not in found:
            # The denied claim went unused, so the cited facts refute each
            # other and the claim holds because nothing does. That is not
            # this method's to emit; a case of a split says so where it
            # supposed the bound that cannot hold.
            return Declined('the cited facts refute each other')
        used = [i for i, k in found.items() if k and i < len(given)]
        self.combining(term, *(where[i][1].rpn(self.flabel) for i in used))
        weight = found[len(given)]
        if claim.how == '=/=':
            return self.stays_apart(used, given, where, claim, scope, facts,
                                    lines)
        if goal.variable is None and goal.label == 'wn':
            return self.negated_order(goal, refs, term, scope, facts, lines,
                                      skip)
        sides = order_sides(goal)
        if sides is None:
            return Declined('the claim states no relation')
        left, right, how = sides
        left, right = left.rpn(self.flabel), right.rpn(self.flabel)
        if len(used) == 1 and given[used[0]].how == '=':
            return self.from_equation(where[used[0]],
                                      found[used[0]] / weight,
                                      left, right, how, scope, facts, lines)
        # What the scaled facts leave over is a constant, and `METHODS.md`
        # says the method may use a closed numeral fact the step does not
        # cite. It is what makes `n! >_ 1` give `n! + 1 > 1`.
        spare = claim.side
        for i in used:
            spare = spare.minus(given[i].side.scaled(found[i] / weight))
        if not spare.constant_only():
            return Declined('what is left over is not a constant')
        return self.from_sum([(where[i], given[i], found[i] / weight)
                              for i in used],
                             left, right, how, spare.constant, scope, facts,
                             lines)

    def by_antisymmetry(self, goal, scope, facts):
        """An equation from the two bounds that close on it.

        A number neither greater nor smaller than another is that number,
        and `letri3` is set.mm saying so. The decision procedure reaches it
        by splitting the claim into its two halves, which is not a split
        any cited line offers, so the two bounds are looked for as they
        stand: Bezout's step 20 has d ≤ gcd(a, b) and gcd(a, b) ≤ d, and
        says the two are equal.
        """
        sides = order_sides(goal)
        if sides is None or sides[2] != '=':
            return None
        a, b = (one.rpn(self.flabel) for one in sides[:2])
        up, down = self.seq(a, b, 'cle', 'wbr'), self.seq(b, a, 'cle', 'wbr')
        if up not in facts or down not in facts:
            return None
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        both = self.seq(up, down, 'wa')
        return work.ap(
            'mpbird', {'ph': scope, 'ps': goal.rpn(self.flabel), 'ch': both},
            work.ap('jca', {'ph': scope, 'ps': up, 'ch': down},
                    facts[up], facts[down]),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(a, 'cr', 'wcel'),
                     'ch': self.seq(b, 'cr', 'wcel'),
                     'th': self.seq(goal.rpn(self.flabel), both, 'wb')},
                    real(a), real(b), work.ap('letri3', {'A': a, 'B': b})))

    def negated_order(self, goal, refs, term, scope, facts, lines, skip):
        """A claim denying a relation, as the relation that holds instead.

        `not ( d ≤ r )` is `r < d`. `linear.fact` has always read it that
        way — `METHODS.md` calls a negation a fact and not a special case —
        and `order_sides` cannot read a denial at all, so such a claim was
        decided and then had nothing to emit. What holds instead is proved
        first, and `ltnle` or `lenlt` turns it round. Those are two of the
        three labels `db/methods.records` names for this method.
        """
        sides = order_sides(goal.children[0])
        if sides is None or sides[2] not in ('<', '<='):
            return Declined('what is denied states no relation')
        a, b = (one.rpn(self.flabel) for one in sides[:2])
        turns, how = (('ltnle', 'clt') if sides[2] == '<='
                      else ('lenlt', 'cle'))
        instead = self.seq(b, a, how, 'wbr')
        held = facts.get(instead)
        if held is None:
            held = self.prove_order(refs, instead, scope, facts, lines, skip)
            if declined(held):
                return held

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        return work.ap(
            'mpbid', {'ph': scope, 'ps': instead, 'ch': term}, held,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(b, 'cr', 'wcel'),
                     'ch': self.seq(a, 'cr', 'wcel'),
                     'th': self.seq(instead, term, 'wb')},
                    real(b), real(a), work.ap(turns, {'A': b, 'B': a})))

    def either_way(self, found, refs, where, given, term, scope, facts,
                   lines, skip):
        """A claim proved twice, once each side of a cited disequality.

        `a ≠ b` is `a < b or b < a`, so a refutation that uses one has to
        try both, and `linear.certificate` says so by returning no single
        combination. Each side is the same claim at a scope one wider, with
        the side's bound standing as a line of its own, so the method proves
        it the way it proves anything; a side that splits again is another
        of these. `mpjaodan` puts the two back together.
        """
        _tag, which = found[0], found[1]
        if which >= len(given):
            return Declined('what splits is the claim, not a citation')
        ref, said = where[which]
        if said.variable is not None or said.label != 'wn' \
                or said.children[0].label != 'wceq':
            return Declined('what splits is not a denied equation')
        a, b = (c.rpn(self.flabel) for c in said.children[0].children)
        below, above = (self.seq(a, b, 'clt', 'wbr'), self.seq(b, a, 'clt', 'wbr'))

        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real(one):
            return self.membership(one, 'cr', scope, facts)

        given = self.cited_fact(ref, said, scope, facts, lines)
        if declined(given):
            return given
        whether = work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(a, b, 'wne'),
                      'ch': self.seq(below, above, 'wo')},
            work.ap('neqned', {'ph': scope, 'A': a, 'B': b}, given),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(a, 'cr', 'wcel'),
                     'ch': self.seq(b, 'cr', 'wcel'),
                     'th': self.seq(self.seq(a, b, 'wne'),
                               self.seq(below, above, 'wo'), 'wb')},
                    real(a), real(b), work.ap('lttri2', {'A': a, 'B': b})))

        frame, sides = len(self.frames), []
        for bound in (below, above):
            inner, lifted = self.widen(scope, facts, bound)
            held = dict(lines)
            held[bound] = Fact(bound, lifted[bound])
            side = self.one_way(bound, term, inner, lifted, held,
                                [*refs, bound],
                                (*skip, said.rpn(self.flabel)))
            if declined(side):
                del self.frames[frame:]
                return side
            sides.append(side)
        del self.frames[frame:]
        return work.ap('mpjaodan',
                       {'ph': scope, 'ps': below, 'ch': term, 'th': above},
                       sides[0], sides[1], whether)

    def one_way(self, bound, term, scope, facts, lines, refs, skip):
        """One side of a split, at the scope that side opened.

        Three ways, in the order they cost. The side's own bound may be the
        claim. The claim may follow from the bound and what is cited, which
        is the method again. Or the bound may contradict what is cited, and
        then the claim holds because nothing does: the case is impossible
        and `METHODS.md` counts it refuted rather than proved.
        """
        if term in facts:
            return facts[term]
        found = self.prove_order(refs, term, scope, facts, lines, skip)
        if not declined(found):
            return found
        return self.impossible(bound, term, scope, facts)

    def impossible(self, bound, term, scope, facts):
        """The claim, because the bound this scope opened cannot hold.

        `lenlt` is what says so: a ≤ b and b < a deny each other, and the
        step already has the first where the case supposes the second.
        """
        node = self.to_term(bound)
        sides = order_sides(node)
        if sides is None or sides[2] != '<':
            return Declined('the bound states no strict order')
        low, high = (one.rpn(self.flabel) for one in sides[:2])
        denies = self.seq(high, low, 'cle', 'wbr')
        if denies not in facts:
            return Declined('nothing in scope denies the bound')

        def real(one):
            return self.membership(one, 'cr', scope, facts)
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        return work.ap(
            'pm2.21dd', {'ph': scope, 'ps': bound, 'ch': term},
            facts[bound],
            work.ap('mpbid', {'ph': scope, 'ps': denies,
                              'ch': self.seq(bound, 'wn')},
                    facts[denies],
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': self.seq(high, 'cr', 'wcel'),
                             'ch': self.seq(low, 'cr', 'wcel'),
                             'th': self.seq(denies, self.seq(bound, 'wn'), 'wb')},
                            real(high), real(low),
                            work.ap('lenlt', {'A': high, 'B': low}))))

    def stays_apart(self, used, given, where, claim, scope, facts, lines):
        """Two things the step says are not equal, because one is below.

        The claim is a denial, so the combination that reaches it is the
        denial supposed and contradicted. Where the contradiction is with
        a single strict bound between the very two the claim names, that
        whole argument is `ltne`: something below another is not it.
        """
        if len(used) != 1 or given[used[0]].how != '<':
            return Declined('not one strict bound')
        ref, said = where[used[0]]
        parts = order_sides(said)
        if parts is None or parts[2] != '<':
            return Declined('the cited bound is not stated as one')
        below = [c.rpn(self.flabel) for c in said.children[:2]]
        # The claim must be about the two the bound is about, and no more.
        if claim.side.minus(given[used[0]].side.scaled(-1)).atoms() \
                or claim.side.minus(
                    given[used[0]].side.scaled(-1)).constant:
            return Declined('the claim is not that bound turned')
        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))

        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        bound = self.cited_fact(ref, said, scope, facts, lines)
        if declined(bound):
            return bound
        return work.ap(
            'neneqd', {'ph': scope, 'A': below[1], 'B': below[0]},
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(below[0], 'cr', 'wcel'),
                     'ch': self.seq(below[0], below[1], 'clt', 'wbr'),
                     'th': self.seq(below[1], below[0], 'wne')},
                    real_number(below[0]), bound,
                    work.ap('ltne', {'A': below[0], 'B': below[1]})))

    def from_sum(self, used, left, right, how, spare, scope, facts, lines):
        """The claim as the cited bounds added, and what they leave over.

        Each says a difference is at most zero; added, the two differences
        are the claim's, which is the normalizer's question. `le2add` is
        the addition, and what it lands on is zero plus zero.

        A claim that is strict gets its strictness from the constant the
        bounds leave over, which is a closed numeral fact the step does
        not cite. `METHODS.md` says the method may use one.
        """
        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        work = normal.Emitter(self.sigs, scope,
                              lambda t: self.membership(t, 'cc', scope, facts))
        # A number is at most itself, and uses no bound at all: the
        # requires line `a ≤ a` of the intermediate value proof's step 1.
        if not used and how == '<=' and spare == 0 and left == right:
            return work.ap('leidd', {'ph': scope, 'A': left},
                           real_number(left))
        # A strict claim whose strictness comes from a cited strict fact,
        # with nothing left over: the facts are added keeping it.
        if how == '<' and spare == 0:
            return self.strictly(work, used, left, right, scope, facts,
                                 lines, real_number)
        if how == '<':
            if spare != -1 or len(used) != 1:
                return Declined('only one bound short of one is '
                                       'written')
        elif how != '<=' or spare != 0:
            return Declined('only one or two bounds is written')
        if not 1 <= len(used) <= 2:
            return Declined('only one or two bounds is written')
        gaps, bounds, real = [], [], []
        for (ref, said), fact, times in used:
            stated = self.cited_fact(ref, said, scope, facts, lines)
            if declined(stated):
                return stated
            made = self.at_most_zero(work, said, fact, times, stated,
                                     real_number)
            if declined(made):
                return made
            one, proof, held = made
            gaps.append(one)
            bounds.append(proof)
            real.append(held)
        if how == '<':
            return self.short_of_one(work, gaps[0], bounds[0], real[0],
                                     left, right, real_number)
        if len(gaps) == 1:
            # Nothing to add: the one bound is already the claim's.
            return self.bound_reaches(work, gaps[0], bounds[0], left, right,
                                      real_number)
        total = self.seq(gaps[0], gaps[1], 'caddc', 'co')
        zero = work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': self.seq(self.seq(gaps[0], 'cc0', 'cle', 'wbr'),
                               self.seq(gaps[1], 'cc0', 'cle', 'wbr'), 'wa'),
                     'ch': self.seq(total, self.seq('cc0', 'cc0', 'caddc', 'co'),
                               'cle', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                    'ch': self.seq(gaps[1], 'cc0', 'cle', 'wbr')},
                            *bounds),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': self.seq(self.seq(self.seq(gaps[0], 'cr', 'wcel'),
                                           self.seq(gaps[1], 'cr', 'wcel'), 'wa'),
                                       self.seq(self.seq('cc0', 'cr', 'wcel'),
                                           self.seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': seq(seq(seq(gaps[0], 'cc0', 'cle', 'wbr'),
                                           seq(gaps[1], 'cc0', 'cle', 'wbr'),
                                           'wa'),
                                       seq(total,
                                           seq('cc0', 'cc0', 'caddc', 'co'),
                                           'cle', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq(self.seq(gaps[0], 'cr', 'wcel'),
                                               self.seq(gaps[1], 'cr', 'wcel'),
                                               'wa'),
                                     'ch': self.seq(self.seq('cc0', 'cr', 'wcel'),
                                               self.seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq(gaps[0], 'cr', 'wcel'),
                                             'ch': self.seq(gaps[1], 'cr',
                                                       'wcel')}, *real),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq('cc0', 'cr', 'wcel'),
                                             'ch': self.seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('le2add', {'A': gaps[0], 'B': gaps[1],
                                               'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return self.bound_reaches(work, total, added, left, right,
                                  real_number)

    def strictly(self, work, used, left, right, scope, facts, lines,
                 real_number):
        """A strict claim from one or two cited bounds, one of them strict.

        Each bound is said as its difference against zero — `sublt0d` for a
        strict one, keeping the strictness, and `difference_le` for one at
        most — and two are added by the lemma their strictness calls for:
        `ltleadd`, `leltadd` or `lt2add`. The sum is the claim's difference,
        which is the normalizer's question, and `sublt0d` turns a
        difference below zero back into the claim. `f(c) < 0` gives
        `0 < −f(c)` this way, and `x₁ − c < δ` gives `x₁ < c + δ`.
        """
        if not 1 <= len(used) <= 2:
            return Declined('only one or two strict bounds is written')
        gaps, bounds, reals, strict = [], [], [], []
        for (ref, said), _fact, times in used:
            if times != 1:
                return Declined(f'a strict bound scaled by {times} is not '
                                f'written')
            given = self.cited_fact(ref, said, scope, facts, lines)
            if declined(given):
                return given
            if said.variable is None and said.label == 'wn' \
                    and len(said.children) == 1:
                made = self.unnegated(work, said.children[0], given,
                                      real_number)
                if declined(made):
                    return made
                said, given = made
            parts = order_sides(said)
            if parts is None or parts[2] not in ('<', '<='):
                return Declined('a strict sum takes bounds, not equations')
            was = [c.rpn(self.flabel) for c in said.children[:2]]
            gap = self.seq(was[0], was[1], 'cmin', 'co')
            if parts[2] == '<':
                bounds.append(work.ap(
                    'mpbird',
                    {'ph': scope, 'ps': self.seq(gap, 'cc0', 'clt', 'wbr'),
                     'ch': self.seq(was[0], was[1], 'clt', 'wbr')},
                    given,
                    work.ap('sublt0d', {'ph': scope, 'A': was[0],
                                        'B': was[1]},
                            real_number(was[0]), real_number(was[1]))))
            else:
                bounds.append(self.difference_le(work, was, given, None,
                                                 real_number))
            strict.append(parts[2] == '<')
            gaps.append(gap)
            reals.append(work.ap(
                'syl2anc', {'ph': scope, 'ps': self.seq(was[0], 'cr', 'wcel'),
                            'ch': self.seq(was[1], 'cr', 'wcel'),
                            'th': self.seq(gap, 'cr', 'wcel')},
                real_number(was[0]), real_number(was[1]),
                work.ap('resubcl', {'A': was[0], 'B': was[1]})))
        if not any(strict):
            return Declined('no cited bound is strict')
        if len(gaps) == 1:
            total, below = gaps[0], bounds[0]
        else:
            total, below = self.added_strictly(work, gaps, bounds, reals,
                                               strict)
        span = self.seq(left, right, 'cmin', 'co')
        alike = self.same_polynomial(work, span, total)
        if declined(alike):
            return alike
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'clt', 'wbr'),
                      'ch': self.seq(left, right, 'clt', 'wbr')},
            work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                'C': 'cc0', 'R': 'clt'}, alike, below),
            work.ap('sublt0d', {'ph': scope, 'A': left, 'B': right},
                    real_number(left), real_number(right)))

    def added_strictly(self, work, gaps, bounds, reals, strict):
        """Two differences against zero added, one strictly below it.

        What comes back is ( scope -> ( g1 + g2 ) < 0 ).
        """
        scope = work.under
        lemma = rules.ADDING[tuple(strict)]
        rel = ['clt' if s else 'cle' for s in strict]
        total = self.seq(gaps[0], gaps[1], 'caddc', 'co')
        zero = work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re')
        sum_zero = self.seq('cc0', 'cc0', 'caddc', 'co')
        each = self.seq(self.seq(gaps[0], 'cc0', rel[0], 'wbr'),
                        self.seq(gaps[1], 'cc0', rel[1], 'wbr'), 'wa')
        reals_pair = self.seq(self.seq(gaps[0], 'cr', 'wcel'),
                              self.seq(gaps[1], 'cr', 'wcel'), 'wa')
        zeros_pair = self.seq(self.seq('cc0', 'cr', 'wcel'),
                              self.seq('cc0', 'cr', 'wcel'), 'wa')
        added = work.ap(
            'mpd', {'ph': scope, 'ps': each,
                    'ch': self.seq(total, sum_zero, 'clt', 'wbr')},
            work.ap('jca', {'ph': scope,
                            'ps': self.seq(gaps[0], 'cc0', rel[0], 'wbr'),
                            'ch': self.seq(gaps[1], 'cc0', rel[1], 'wbr')},
                    *bounds),
            work.ap('syl',
                    {'ph': scope,
                     'ps': self.seq(reals_pair, zeros_pair, 'wa'),
                     'ch': self.seq(each,
                                    self.seq(total, sum_zero, 'clt', 'wbr'),
                                    'wi')},
                    work.ap('jca', {'ph': scope, 'ps': reals_pair,
                                    'ch': zeros_pair},
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq(gaps[0], 'cr', 'wcel'),
                                     'ch': self.seq(gaps[1], 'cr', 'wcel')},
                                    *reals),
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq('cc0', 'cr', 'wcel'),
                                     'ch': self.seq('cc0', 'cr', 'wcel')},
                                    zero, zero)),
                    work.ap(lemma, {'A': gaps[0], 'B': gaps[1],
                                    'C': 'cc0', 'D': 'cc0'})))
        return total, work.ap(
            'breqtrd', {'ph': scope, 'A': total, 'B': sum_zero, 'C': 'cc0',
                        'R': 'clt'},
            added,
            work.a1i(self.seq(sum_zero, 'cc0', 'wceq'), '00id'))

    def short_of_one(self, work, gap, bound, gap_real, left, right,
                     real_number):
        """A bound and a minus one, added, to reach a strict claim.

        `leltadd` is the addition that keeps the strictness, and the claim
        comes back through `ltsubadd` with nothing on the right and `addlid`
        to tidy it. `strictly` turns a difference back with `sublt0d`;
        both are sound, and moving this route onto it would change the
        files it writes and prove nothing more.
        """
        scope = work.under
        minus, span = self.seq('c1', 'cneg'), self.seq(left, right, 'cmin', 'co')
        total = self.seq(gap, minus, 'caddc', 'co')
        alike = self.same_polynomial(work, span, total)
        if declined(alike):
            return alike
        zero = work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re')
        pair = seq(seq(gap, 'cr', 'wcel'), seq(minus, 'cr', 'wcel'), 'wa')
        added = work.ap(
            'breqtrd', {'ph': scope, 'A': total,
                        'B': self.seq('cc0', 'cc0', 'caddc', 'co'), 'C': 'cc0',
                        'R': 'clt'},
            work.ap('mpd',
                    {'ph': scope,
                     'ps': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                               self.seq(minus, 'cc0', 'clt', 'wbr'), 'wa'),
                     'ch': self.seq(total, self.seq('cc0', 'cc0', 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('jca', {'ph': scope,
                                    'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                                    'ch': self.seq(minus, 'cc0', 'clt', 'wbr')},
                            bound,
                            work.a1i(self.seq(minus, 'cc0', 'clt', 'wbr'),
                                     'neg1lt0')),
                    work.ap('syl',
                            {'ph': scope,
                             'ps': self.seq(pair,
                                       self.seq(self.seq('cc0', 'cr', 'wcel'),
                                           self.seq('cc0', 'cr', 'wcel'), 'wa'),
                                       'wa'),
                             'ch': self.seq(self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                                           self.seq(minus, 'cc0', 'clt', 'wbr'),
                                           'wa'),
                                       self.seq(total,
                                           self.seq('cc0', 'cc0', 'caddc', 'co'),
                                           'clt', 'wbr'), 'wi')},
                            work.ap('jca',
                                    {'ph': scope, 'ps': pair,
                                     'ch': self.seq(self.seq('cc0', 'cr', 'wcel'),
                                               self.seq('cc0', 'cr', 'wcel'),
                                               'wa')},
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq(gap, 'cr', 'wcel'),
                                             'ch': self.seq(minus, 'cr', 'wcel')},
                                            gap_real,
                                            self.real_numeral(
                                                work, Fraction(-1))),
                                    work.ap('jca',
                                            {'ph': scope,
                                             'ps': self.seq('cc0', 'cr', 'wcel'),
                                             'ch': self.seq('cc0', 'cr', 'wcel')},
                                            zero, zero)),
                            work.ap('leltadd', {'A': gap, 'B': minus,
                                                'C': 'cc0', 'D': 'cc0'}))),
            work.a1i(self.seq(self.seq('cc0', 'cc0', 'caddc', 'co'), 'cc0', 'wceq'),
                     '00id'))
        return work.ap(
            'breqtrd', {'ph': scope, 'A': left,
                        'B': self.seq('cc0', right, 'caddc', 'co'), 'C': right,
                        'R': 'clt'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': self.seq(span, 'cc0', 'clt', 'wbr'),
                     'ch': self.seq(left, self.seq('cc0', right, 'caddc', 'co'),
                               'clt', 'wbr')},
                    work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                        'C': 'cc0', 'R': 'clt'},
                            alike, added),
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                             'ch': self.seq(right, 'cr', 'wcel'),
                             'th': self.seq('cc0', 'cr', 'wcel'),
                             'ta': self.seq(self.seq(span, 'cc0', 'clt', 'wbr'),
                                       self.seq(left,
                                           self.seq('cc0', right, 'caddc', 'co'),
                                           'clt', 'wbr'), 'wb')},
                            real_number(left), real_number(right), zero,
                            work.ap('ltsubadd', {'A': left, 'B': right,
                                                 'C': 'cc0'}))),
            work.ap('syl', {'ph': scope, 'ps': self.seq(right, 'cc', 'wcel'),
                            'ch': self.seq(self.seq('cc0', right, 'caddc', 'co'),
                                      right, 'wceq')},
                    work.ap('recnd', {'ph': scope, 'A': right},
                            real_number(right)),
                    work.ap('addlid', {'A': right})))

    def bound_reaches(self, work, total, added, left, right, real_number):
        """A term at most zero, said of the claim's two sides.

        The normalizer says the term is the claim's difference, and
        `suble0` says a difference at most zero is `<_` between them.
        """
        scope, span = work.under, self.seq(left, right, 'cmin', 'co')
        alike = self.same_polynomial(work, span, total)
        if declined(alike):
            return alike
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': self.seq(left, right, 'cle', 'wbr')},
            work.ap('eqbrtrd', {'ph': scope, 'A': span, 'B': total,
                                'C': 'cc0', 'R': 'cle'},
                    alike, added),
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                     'ch': self.seq(right, 'cr', 'wcel'),
                     'th': self.seq(self.seq(span, 'cc0', 'cle', 'wbr'),
                               self.seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def at_most_zero(self, work, said, fact, times, given, real_number):
        """One cited fact, scaled, as a term that is at most zero.

        Everything a sum takes is brought to that one shape first, so the
        addition has one case rather than one per relation. An equation is
        at most zero because it is zero exactly; an inequality already is,
        and scaling it by something positive leaves it so.
        """
        scope = work.under
        if said.variable is None and said.label == 'wn' \
                and len(said.children) == 1:
            made = self.unnegated(work, said.children[0], given, real_number)
            if declined(made):
                return made
            said, given = made
        parts = order_sides(said)
        if parts is None:
            return Declined('a cited fact states no relation')
        was = [c.rpn(self.flabel) for c in said.children[:2]]
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        real = work.ap('syl2anc',
                       {'ph': scope, 'ps': self.seq(was[0], 'cr', 'wcel'),
                        'ch': self.seq(was[1], 'cr', 'wcel'),
                        'th': self.seq(gap, 'cr', 'wcel')},
                       real_number(was[0]), real_number(was[1]),
                       work.ap('resubcl', {'A': was[0], 'B': was[1]}))
        numeral = field.spell_coefficient(times)
        if numeral is None:
            return Declined(f'{times} is past one digit')
        scaled = self.seq(numeral, gap, 'cmul', 'co')
        scaled_real = work.ap(
            'syl2anc', {'ph': scope, 'ps': self.seq(numeral, 'cr', 'wcel'),
                        'ch': self.seq(gap, 'cr', 'wcel'),
                        'th': self.seq(scaled, 'cr', 'wcel')},
            self.real_numeral(work, times), real,
            work.ap('remulcl', {'A': numeral, 'B': gap}))
        if parts[2] == '=':
            vanishes = work.chain(
                work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                   'C': numeral, 'F': 'cmul'},
                        self.difference_zero(work, was, given)),
                work.ap('syl', {'ph': scope,
                                'ps': self.seq(numeral, 'cc', 'wcel'),
                                'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                          'cc0', 'wceq')},
                        work.coefficient(times),
                        work.ap('mul01', {'A': numeral})),
                scaled, self.seq(numeral, 'cc0', 'cmul', 'co'), 'cc0')
            return scaled, work.ap(
                'eqled', {'ph': scope, 'A': scaled, 'B': 'cc0'},
                scaled_real, vanishes), scaled_real
        if parts[2] == '<':
            # A sum that lands on `at most` has no use for the strictness,
            # so it is given up here and the one case below serves both.
            given = work.ap('ltled', {'ph': scope, 'A': was[0],
                                      'B': was[1]},
                            real_number(was[0]), real_number(was[1]), given)
        elif parts[2] != '<=':
            return Declined(f'a cited {parts[2]} is not written')
        bound = self.difference_le(work, was, given, None, real_number)
        if times == 1:
            return gap, bound, real
        if times <= 0:
            return Declined('a bound may only be scaled upward')
        return scaled, work.ap(
            'breqtrd', {'ph': scope, 'A': scaled,
                        'B': self.seq(numeral, 'cc0', 'cmul', 'co'), 'C': 'cc0',
                        'R': 'cle'},
            work.ap('mpbid',
                    {'ph': scope, 'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                     'ch': self.seq(scaled, self.seq(numeral, 'cc0', 'cmul', 'co'),
                               'cle', 'wbr')},
                    bound,
                    work.ap('syl3anc',
                            {'ph': scope, 'ps': self.seq(gap, 'cr', 'wcel'),
                             'ch': self.seq('cc0', 'cr', 'wcel'),
                             'th': self.seq(self.seq(numeral, 'cr', 'wcel'),
                                       self.seq('cc0', numeral, 'clt', 'wbr'),
                                       'wa'),
                             'ta': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                                       self.seq(scaled,
                                           self.seq(numeral, 'cc0', 'cmul', 'co'),
                                           'cle', 'wbr'), 'wb')},
                            real, work.a1i(self.seq('cc0', 'cr', 'wcel'), '0re'),
                            work.ap('jca',
                                    {'ph': scope,
                                     'ps': self.seq(numeral, 'cr', 'wcel'),
                                     'ch': self.seq('cc0', numeral, 'clt',
                                               'wbr')},
                                    self.real_numeral(work, times),
                                    work.a1i(self.seq('cc0', numeral, 'clt',
                                                 'wbr'),
                                             f'{times.numerator}pos')),
                            work.ap('lemul2', {'A': gap, 'B': 'cc0',
                                               'C': numeral}))),
            work.ap('syl', {'ph': scope, 'ps': self.seq(numeral, 'cc', 'wcel'),
                            'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                      'cc0', 'wceq')},
                    work.coefficient(times),
                    work.ap('mul01', {'A': numeral}))), scaled_real

    def unnegated(self, work, inner, given, real_number):
        """A cited fact stated as a denial, said the other way round.

        `prime-above` reaches its bound by supposing the opposite and
        finding no witness, so what it has is `-. A < m` where the method
        wants `m <_ A`. `lenlt` is the one saying those are the same, and
        `ltnle` the same the other way round: the intermediate value proof
        supposes `not s ≤ c − δ` and wants `c − δ < s`.
        """
        parts = order_sides(inner)
        if parts is None or parts[2] not in rules.DENIED:
            return Declined('only a denied `<` or `≤` is turned round')
        denied, said, lemma = rules.DENIED[parts[2]]
        was = [c.rpn(self.flabel) for c in inner.children[:2]]
        turned = self.to_term(self.seq(was[1], was[0], said, 'wbr'))
        return turned, work.ap(
            'mpbird', {'ph': work.under,
                       'ps': self.seq(was[1], was[0], said, 'wbr'),
                       'ch': self.seq(self.seq(was[0], was[1], denied, 'wbr'),
                                      'wn')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': self.seq(was[1], 'cr', 'wcel'),
                     'ch': self.seq(was[0], 'cr', 'wcel'),
                     'th': self.seq(self.seq(was[1], was[0], said, 'wbr'),
                               self.seq(self.seq(was[0], was[1], denied, 'wbr'),
                                        'wn'),
                               'wb')},
                    real_number(was[1]), real_number(was[0]),
                    work.ap(lemma, {'A': was[1], 'B': was[0]})))

    def real_numeral(self, work, times):
        """( scope -> n e. RR ) for a whole multiplier."""
        whole = abs(times.numerator)
        held = work.a1i(self.seq(field.NUMERAL[whole], 'cr', 'wcel'),
                        f'{whole}re')
        if times.numerator >= 0:
            return held
        return work.ap('renegcld', {'ph': work.under,
                                    'A': field.NUMERAL[whole]}, held)

    def cited_fact(self, ref, said, scope, facts, lines):
        """The proof of one fact a cited line states.

        A line may say several things at once — `abs-bounds` concludes a
        pair of bounds — and what the step uses is one of them, so the
        line is taken apart the way `opposing` takes one apart.
        """
        want = said.rpn(self.flabel)
        held = self.carried(ref, facts, lines)
        if lines[ref].term == want:
            return held
        known = dict(facts)
        self.unpack(lines[ref].term, held, scope, known)
        if want not in known:
            return Declined('that line does not reach the fact')
        return known[want]

    def difference_le(self, work, was, given, facts, real_number):
        """( scope -> ( A - B ) <_ 0 ) from a cited A <_ B."""
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        return work.ap(
            'mpbird', {'ph': work.under, 'ps': self.seq(gap, 'cc0', 'cle', 'wbr'),
                       'ch': self.seq(was[0], was[1], 'cle', 'wbr')},
            given,
            work.ap('syl2anc',
                    {'ph': work.under, 'ps': self.seq(was[0], 'cr', 'wcel'),
                     'ch': self.seq(was[1], 'cr', 'wcel'),
                     'th': self.seq(self.seq(gap, 'cc0', 'cle', 'wbr'),
                               self.seq(was[0], was[1], 'cle', 'wbr'), 'wb')},
                    real_number(was[0]), real_number(was[1]),
                    work.ap('suble0', {'A': was[0], 'B': was[1]})))

    def from_equation(self, cited, times, left, right, how, scope, facts,
                      lines):
        """The claim as one cited equation, scaled.

        An equation may be multiplied by anything, which is what lets one
        cited equation carry a claim on its own. A combination that uses
        an inequality needs that inequality scaled and added, and is a
        different proof.
        """
        ref, said = cited
        parts = order_sides(said)
        if parts is None or parts[2] != '=':
            return Declined('the cited fact is not an equation')
        numeral = field.spell_coefficient(times)
        if numeral is None:
            return Declined(f'{times} is past one digit')

        def complex_number(term):
            return self.membership(term, 'cc', scope, facts)

        work = normal.Emitter(self.sigs, scope, complex_number)
        was = [c.rpn(self.flabel) for c in said.children]
        gap = self.seq(was[0], was[1], 'cmin', 'co')
        scaled = self.seq(numeral, gap, 'cmul', 'co')
        span = self.seq(left, right, 'cmin', 'co')
        def real_number(one):
            return self.membership(one, 'cr', scope, facts)

        if parts[2] == '=':
            # The cited equation says its difference is zero; scaled, that
            # is the claim's difference, and the normalizer is what says so.
            alike = self.same_polynomial(work, span, scaled)
            stated = self.cited_fact(ref, said, scope, facts, lines)
            for one in (alike, stated):
                if declined(one):
                    return one
            reached = work.chain(
                alike,
                work.chain(
                    work.ap('oveq2d', {'ph': scope, 'A': gap, 'B': 'cc0',
                                       'C': numeral, 'F': 'cmul'},
                            self.difference_zero(work, was, stated)),
                    work.ap('syl',
                            {'ph': scope, 'ps': self.seq(numeral, 'cc', 'wcel'),
                             'ch': self.seq(self.seq(numeral, 'cc0', 'cmul', 'co'),
                                       'cc0', 'wceq')},
                            work.coefficient(times),
                            work.ap('mul01', {'A': numeral})),
                    scaled, self.seq(numeral, 'cc0', 'cmul', 'co'), 'cc0'),
                span, scaled, 'cc0')
            if how == '=':
                return work.ap(
                    'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'wceq'),
                              'ch': self.seq(left, right, 'wceq')},
                    reached,
                    work.ap('syl2anc',
                            {'ph': scope, 'ps': self.seq(left, 'cc', 'wcel'),
                             'ch': self.seq(right, 'cc', 'wcel'),
                             'th': self.seq(self.seq(span, 'cc0', 'wceq'),
                                       self.seq(left, right, 'wceq'), 'wb')},
                            complex_number(left), complex_number(right),
                            work.ap('subeq0', {'A': left, 'B': right})))
            if how != '<=':
                return Declined(f'a {how} conclusion is not written')
            # A difference that is zero is at most zero.
            at_most = work.ap(
                'eqled', {'ph': scope, 'A': span, 'B': 'cc0'},
                work.ap('syl2anc',
                        {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                         'ch': self.seq(right, 'cr', 'wcel'),
                         'th': self.seq(span, 'cr', 'wcel')},
                        real_number(left), real_number(right),
                        work.ap('resubcl', {'A': left, 'B': right})),
                reached)
        else:
            return Declined(f'a {how} conclusion is not written')
        # A difference at most zero is what `<_` says of the two sides.
        return work.ap(
            'mpbid', {'ph': scope, 'ps': self.seq(span, 'cc0', 'cle', 'wbr'),
                      'ch': self.seq(left, right, 'cle', 'wbr')},
            at_most,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(left, 'cr', 'wcel'),
                     'ch': self.seq(right, 'cr', 'wcel'),
                     'th': self.seq(self.seq(span, 'cc0', 'cle', 'wbr'),
                               self.seq(left, right, 'cle', 'wbr'), 'wb')},
                    real_number(left), real_number(right),
                    work.ap('suble0', {'A': left, 'B': right})))

    def difference_zero(self, work, was, given):
        """( scope -> ( A - B ) = 0 ) from a cited A = B."""
        scope = work.under
        return work.ap(
            'mpbird', {'ph': scope, 'ps': self.seq(self.seq(was[0], was[1], 'cmin',
                                                  'co'), 'cc0', 'wceq'),
                       'ch': self.seq(was[0], was[1], 'wceq')},
            given,
            work.ap('syl2anc',
                    {'ph': scope, 'ps': self.seq(was[0], 'cc', 'wcel'),
                     'ch': self.seq(was[1], 'cc', 'wcel'),
                     'th': seq(seq(seq(was[0], was[1], 'cmin', 'co'), 'cc0',
                                   'wceq'), seq(was[0], was[1], 'wceq'),
                               'wb')},
                    work.atom(was[0]), work.atom(was[1]),
                    work.ap('subeq0', {'A': was[0], 'B': was[1]})))

    def decide_order(self, step, term, lines):
        """Refuse an `inequalities` step that does not follow from its lines.

        A cited line of several sentences supplies each sentence that is a
        linear fact and is ignored for the rest, so citing a line that also
        states a membership is not an error.
        """
        claim = linear.fact(self.to_term(term), self.flabel)
        if claim is None:
            return                               # not a relation this decides
        given = []
        for ref in step.just.refs:
            held = lines.get(ref)
            if held is None:
                continue
            for said in self.parts(held.term):
                one = linear.fact(self.to_term(said), self.flabel)
                if one is not None:
                    given.append(one)
        if not linear.follows(given, claim):
            raise self.defect(step.line,
                              f'{self.render(term)} does not follow from what '
                              f'step {fmt(step.number)} cites')

    def assume(self, step, term, scope, facts, prefix, lines):
        """State what a step claims, under everything it rests on, and take
        it. What the file assumes is listed at its head.

        Everything it rests on is the lines it cites as well as the
        conditions it writes. A step reading `inequalities, from 3, 4` that
        assumed only its `requires` lines would assume that the sum of two
        numbers is at most the sum of their absolute values, which is the
        theorem; under the lines it cites it assumes only that two
        inequalities may be added, which is what the method is for. The
        cited lines are also why the file needs the proofs above it: an
        assumption that drops them leaves them unused and unchecked.
        """
        asks = []
        for ref in step.just.refs:
            cited = lines[ref]
            asks.append((cited.term, self.carried(ref, facts, lines)))
        for want, (_t, how, line) in zip(
                [self.read(t) for t, _h, _l in step.requires], step.requires,
                strict=True):
            here = self.term(want)
            if here not in [a for a, _p in asks]:
                # Proved from its reason and checked against it, as
                # `supplied` and `required` prove one, so the step rests on
                # the line and not on whatever the line was proved from.
                made = self.side(want, how, scope, facts, step)
                if not declined(made):
                    made = self.discharged_by(made, step, how, line)
                asks.append((here, made))

        statement = term
        for one, _given in reversed(asks):
            statement = self.seq(one, statement, 'wi')
        proof = self.stated(prefix, '|- ' + self.render(statement))
        if not asks:
            # Nothing to discharge, so the statement is simply taken at the
            # scope the step sits in.
            return self.seq(term, scope, proof, 'a1i')
        # The conditions nest, outermost first, so each is answered in turn
        # and what is left of the statement shrinks by one.
        for i, (one, given) in enumerate(asks):
            rest = term
            for later, _p in reversed(asks[i + 1:]):
                rest = self.seq(later, rest, 'wi')
            proof = self.seq(scope, one, rest, given, proof,
                        'syl' if i == 0 else 'mpd')
        return proof

    def stated(self, prefix, text):
        """Register a statement this file takes rather than proves.

        What a statement asks to be pushed is every variable it mentions, in
        the order the database declares them, which is not the order the
        statement happens to write them in. The same statement asked for
        twice is listed once: two steps may need the same arithmetic.
        """
        if text in self.assumed:
            return self.assumed[text]
        label = self.fresh(prefix)
        self.axioms.append((label, text))
        free = sorted({t for t in text.split() if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$a', text.split(),
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])
        self.assumed[text] = self.seq(*(self.flabel[v] for v in free), label)
        return self.assumed[text]
