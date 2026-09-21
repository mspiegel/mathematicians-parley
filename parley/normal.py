"""Metamath proofs of ring identities over ℂ.

`field.py` decides whether an `algebra` step holds; this builds the proof of
one that does. The two are separate because deciding needs no kernel and
emitting is most of the work.

A step claims `L = R` where both sides are the same polynomial. The proof is
that each side equals one canonical term — `field.spell` of that polynomial —
so what is needed is a procedure taking a term to its canonical form and
saying why. That is done by recursion on the term rather than by searching
for a chain of rewrites: at `a + b` both sides are already canonical, and
what remains is to add two canonical forms, which is a merge.

Every step carries its membership alongside its equality. A ring lemma wants
its arguments in ℂ, and a canonical form's membership is built as the form is
built rather than asked for again at each use: `m ∈ ℂ` is proved once, and
everything above it follows by `mulcld`, `addcld` and `expcld`. Asking each
time would re-derive the same fact for every subterm of every intermediate
form, which is the shape of slowdown this project has met before.

`elaborate.py` drives this; nothing here reads the database or the corpus.
"""
from fractions import Fraction

import field
from field import NUMERAL, order, spell_monomial

ADD, MUL, EXP, DIV = 'caddc', 'cmul', 'cexp', 'cdiv'


def seq(*parts):
    return ' '.join(p for p in parts if p)


def op(left, right, what):
    """`( left what right )`, which reverse Polish writes the other way."""
    return seq(left, right, what, 'co')


def join(terms, what=ADD):
    """A left-associated run, which is the shape every canonical form has."""
    out = terms[0]
    for one in terms[1:]:
        out = op(out, one, what)
    return out


class Emitter:
    """Proofs over one scope.

    `under` is the antecedent every statement carries, in reverse Polish.
    `atom` is asked for the membership of a term the recursion bottoms out
    at, and is the one thing this module cannot do for itself."""

    def __init__(self, sigs, under, atom, apart=None):
        self.sigs = sigs
        self.under = under
        self.atom = atom                  # rpn -> ( under -> rpn e. CC )
        self.apart = apart                # rpn -> ( under -> rpn =/= 0 )
        self.flabel = {s.statement[1]: label
                       for label, s in sigs.items() if s.kind == '$f'}
        self.held = {}                    # rpn -> membership, proved once

    def ap(self, label, binds=None, *essentials):
        sig = self.sigs[label]
        out = [binds[var] if binds and var in binds else self.flabel[var]
               for _typecode, var in sig.floats]
        return seq(*out, *essentials, label)

    def same(self, what):
        """( under -> what = what )."""
        return self.ap('eqidd', {'ph': self.under, 'A': what})

    def chain(self, first, second, a, b, c):
        """( under -> a = c ) from ( under -> a = b ) and ( under -> b = c )."""
        return self.ap('eqtrd', {'ph': self.under, 'A': a, 'B': b, 'C': c},
                       first, second)

    # --- membership -------------------------------------------------------

    @staticmethod
    def complex_label(value):
        """What says a numeral is a complex number.

        set.mm proves one for each digit but takes the one for 1 as an
        axiom, so that digit is named differently from the rest."""
        return 'ax-1cn' if value == 1 else f'{value}cn'

    @staticmethod
    def apart_label(value):
        """What says a numeral is not zero, named the same way."""
        return 'ax-1ne0' if value == 1 else f'{value}ne0'

    def number(self, value):
        """( under -> n e. CC ) for a whole number the kernel spells."""
        return self.ap('a1i', {'ph': seq(NUMERAL[value], 'cc', 'wcel'),
                               'ps': self.under}, self.complex_label(value))

    def index(self, value):
        """( under -> k e. NN0 ), which an exponent has to be."""
        return self.ap('a1i', {'ph': seq(NUMERAL[value], 'cn0', 'wcel'),
                               'ps': self.under}, f'{value}nn0')

    def coefficient(self, weight):
        """( under -> c e. CC ) for a coefficient, negated where negative."""
        whole = abs(weight.numerator)
        held = self.number(whole)
        if weight.numerator < 0:
            return self.ap('negcld', {'ph': self.under,
                                      'A': NUMERAL[whole]}, held)
        return held

    def monomial_cc(self, monomial):
        """( under -> M e. CC ) for a monomial's canonical form."""
        if not monomial:
            return self.number(1)
        said, out = None, None
        for name, power in monomial:
            one = self.ap('expcld', {'ph': self.under, 'A': name,
                                     'N': NUMERAL[power]},
                          self.atom(name), self.index(power))
            spelt = op(name, NUMERAL[power], EXP)
            if said is None:
                said, out = spelt, one
            else:
                out = self.ap('mulcld', {'ph': self.under, 'A': said,
                                         'B': spelt}, out, one)
                said = op(said, spelt, MUL)
        return out

    def term_cc(self, monomial, weight):
        """( under -> ( c x. M ) e. CC )."""
        return self.ap('mulcld',
                       {'ph': self.under,
                        'A': field.spell_coefficient(weight),
                        'B': spell_monomial(monomial)},
                       self.coefficient(weight), self.monomial_cc(monomial))

    @staticmethod
    def spell_term(item):
        monomial, weight = item
        return op(field.spell_coefficient(weight),
                  spell_monomial(monomial), MUL)

    def spell_run(self, items):
        """A run of terms as one term; the empty run is zero."""
        return (NUMERAL[0] if not items
                else join([self.spell_term(i) for i in items]))

    def run_cc(self, items):
        """( under -> spell_run(items) e. CC ), remembered once per run."""
        said = self.spell_run(items)
        if said in self.held:
            return self.held[said]
        if not items:
            out = self.number(0)
        else:
            out = self.term_cc(*items[0])
            running = self.spell_term(items[0])
            for item in items[1:]:
                one = self.spell_term(item)
                out = self.ap('addcld', {'ph': self.under, 'A': running,
                                         'B': one}, out, self.term_cc(*item))
                running = op(running, one, ADD)
        self.held[said] = out
        return out

    def poly_cc(self, poly):
        return self.run_cc(terms_of(poly))

    # --- moving a term along a sum ---------------------------------------

    def lift(self, proof, left, right, tail, what=ADD):
        """Carry an equality of a prefix out to the whole run.

        A canonical form associates to the left, so a rewrite of the first
        k parts sits under one `oveq1d` for each part after them. Sums and
        products are the same shape, which is why this takes the operation
        rather than assuming one."""
        for one in tail:
            proof = self.ap('oveq1d',
                            {'ph': self.under, 'A': left, 'B': right,
                             'C': one, 'F': what}, proof)
            left, right = op(left, one, what), op(right, one, what)
        return proof

    def swap(self, items, at):
        """Two neighbours exchanged, as an equality of the whole run.

        `add32` says `( ( A + B ) + C ) = ( ( A + C ) + B )`, which is the
        swap when the two sit at the end of a run; `addcom` is the case
        where they are the whole of it. Either way the terms after them
        come along under `lift`."""
        head = items[:at]
        a, b = self.spell_term(items[at]), self.spell_term(items[at + 1])
        tail = [self.spell_term(i) for i in items[at + 2:]]
        if head:
            prefix = self.spell_run(head)
            before = op(op(prefix, a, ADD), b, ADD)
            after = op(op(prefix, b, ADD), a, ADD)
            step = self.ap('syl3anc',
                           {'ph': self.under, 'ps': seq(prefix, 'cc', 'wcel'),
                            'ch': seq(a, 'cc', 'wcel'),
                            'th': seq(b, 'cc', 'wcel'),
                            'ta': seq(before, after, 'wceq')},
                           self.run_cc(head), self.term_cc(*items[at]),
                           self.term_cc(*items[at + 1]),
                           self.ap('add32', {'A': prefix, 'B': a, 'C': b}))
        else:
            before, after = op(a, b, ADD), op(b, a, ADD)
            step = self.ap('syl2anc',
                           {'ph': self.under, 'ps': seq(a, 'cc', 'wcel'),
                            'ch': seq(b, 'cc', 'wcel'),
                            'th': seq(before, after, 'wceq')},
                           self.term_cc(*items[at]),
                           self.term_cc(*items[at + 1]),
                           self.ap('addcom', {'A': a, 'B': b}))
        return self.lift(step, before, after, tail)


    # --- coefficients -----------------------------------------------------

    def a1i(self, claim, proof):
        """( under -> claim ) from a claim that holds outright."""
        return self.ap('a1i', {'ph': claim, 'ps': self.under}, proof)

    def coefficient_sum(self, first, second):
        """( under -> ( c + d ) = e ), the coefficients as `spell` writes them.

        set.mm names a lemma for every pair of single digits, and the pairs
        it leaves out are exactly those with a zero, which `addlid` and
        `addrid` cover. A pair that cancels is `negidd`. Anything else is
        refused rather than guessed at: the step stays assumed, which is
        what it already was."""
        total = first + second
        said = field.spell_coefficient(total)
        c, d = (field.spell_coefficient(first),
                field.spell_coefficient(second))
        if said is None or c is None or d is None:
            raise Unhandled(f'{first} + {second} is past one digit')
        claim = seq(op(c, d, ADD), said, 'wceq')
        a, b = first.numerator, second.numerator
        if a == -b and a != 0:
            whole = NUMERAL[abs(a)]
            cancels = self.ap('negidd', {'ph': self.under, 'A': whole},
                              self.number(abs(a)))
            if a > 0:
                return cancels
            # The negative one first, so the two are commuted before they
            # cancel: `negid` states the sum only one way round.
            return self.chain(
                self.ap('syl2anc',
                        {'ph': self.under, 'ps': seq(c, 'cc', 'wcel'),
                         'ch': seq(d, 'cc', 'wcel'),
                         'th': seq(op(c, d, ADD), op(d, c, ADD), 'wceq')},
                        self.coefficient(first), self.coefficient(second),
                        self.ap('addcom', {'A': c, 'B': d})),
                cancels, op(c, d, ADD), op(d, c, ADD), NUMERAL[0])
        if a < 0 and b < 0:
            # -u i + -u j is -u ( i + j ), which `negdi` says read
            # backwards, and the two are then both positive.
            whole = [NUMERAL[-a], NUMERAL[-b]]
            return self.chain(
                self.ap('eqcomd',
                        {'ph': self.under, 'A': op(c, d, ADD),
                         'B': seq(op(*whole, ADD), 'cneg')},
                        self.ap('syl2anc',
                                {'ph': self.under,
                                 'ps': seq(whole[0], 'cc', 'wcel'),
                                 'ch': seq(whole[1], 'cc', 'wcel'),
                                 'th': seq(seq(op(*whole, ADD), 'cneg'),
                                           op(c, d, ADD), 'wceq')},
                                self.number(-a), self.number(-b),
                                self.ap('negdi', {'A': whole[0],
                                                  'B': whole[1]}))),
                self.ap('negeqd',
                        {'ph': self.under, 'A': op(*whole, ADD),
                         'B': NUMERAL[-a - b]},
                        self.coefficient_sum(-first, -second)),
                op(c, d, ADD), seq(op(*whole, ADD), 'cneg'), said)
        if a < 0 or b < 0:
            if a < 0:
                # The negative one second, so one case covers both.
                return self.chain(
                    self.ap('syl2anc',
                            {'ph': self.under, 'ps': seq(c, 'cc', 'wcel'),
                             'ch': seq(d, 'cc', 'wcel'),
                             'th': seq(op(c, d, ADD), op(d, c, ADD),
                                       'wceq')},
                            self.coefficient(first), self.coefficient(second),
                            self.ap('addcom', {'A': c, 'B': d})),
                    self.coefficient_sum(second, first),
                    op(c, d, ADD), op(d, c, ADD), said)
            return self.minus_numeral(a, -b, c, d, said)
        if a == 0:
            return self.a1i(claim, self.mp(seq(d, 'cc', 'wcel'), claim,
                                           self.complex_label(b),
                                           self.ap('addlid', {'A': d})))
        if b == 0:
            return self.a1i(claim, self.mp(seq(c, 'cc', 'wcel'), claim,
                                           self.complex_label(a),
                                           self.ap('addrid', {'A': c})))
        return self.a1i(claim, f'{a}p{b}e{a + b}')

    def mp(self, given, claim, hypothesis, implication):
        return self.ap('ax-mp', {'ph': given, 'ps': claim},
                       hypothesis, implication)

    def gap_numeral(self, bigger, smaller):
        """( under -> ( i - j ) = k ) for whole numbers with i at least j.

        `subadd` says a difference is a number exactly when adding that
        number back gives the first, so the subtraction is answered out of
        the addition table and set.mm needs no second one."""
        left, right = NUMERAL[bigger], NUMERAL[smaller]
        out = NUMERAL[bigger - smaller]
        return self.ap(
            'mpbird',
            {'ph': self.under,
             'ps': seq(op(left, right, 'cmin'), out, 'wceq'),
             'ch': seq(op(right, out, ADD), left, 'wceq')},
            self.coefficient_sum(Fraction(smaller),
                                 Fraction(bigger - smaller)),
            self.ap('syl3anc',
                    {'ph': self.under, 'ps': seq(left, 'cc', 'wcel'),
                     'ch': seq(right, 'cc', 'wcel'),
                     'th': seq(out, 'cc', 'wcel'),
                     'ta': seq(seq(op(left, right, 'cmin'), out, 'wceq'),
                               seq(op(right, out, ADD), left, 'wceq'),
                               'wb')},
                    self.number(bigger), self.number(smaller),
                    self.number(bigger - smaller),
                    self.ap('subadd', {'A': left, 'B': right, 'C': out})))

    def minus_numeral(self, first, second, c, d, said):
        """( under -> ( i + -u j ) = k ), the two of opposite sign.

        `negsub` turns the sum into a difference, and which way round the
        difference goes decides whether the answer carries a minus."""
        gap = op(NUMERAL[first], NUMERAL[second], 'cmin')
        return self.chain(
            self.ap('syl2anc',
                    {'ph': self.under,
                     'ps': seq(NUMERAL[first], 'cc', 'wcel'),
                     'ch': seq(NUMERAL[second], 'cc', 'wcel'),
                     'th': seq(op(c, d, ADD), gap, 'wceq')},
                    self.number(first), self.number(second),
                    self.ap('negsub', {'A': NUMERAL[first],
                                       'B': NUMERAL[second]})),
            self.same_gap(first, second), op(c, d, ADD), gap, said)

    def same_gap(self, first, second):
        """( under -> ( i - j ) = k ), whichever way round the two are."""
        if first >= second:
            return self.gap_numeral(first, second)
        other = op(NUMERAL[second], NUMERAL[first], 'cmin')
        return self.chain(
            self.ap('eqcomd',
                    {'ph': self.under, 'A': seq(other, 'cneg'),
                     'B': op(NUMERAL[first], NUMERAL[second], 'cmin')},
                    self.ap('syl2anc',
                            {'ph': self.under,
                             'ps': seq(NUMERAL[second], 'cc', 'wcel'),
                             'ch': seq(NUMERAL[first], 'cc', 'wcel'),
                             'th': seq(seq(other, 'cneg'),
                                       op(NUMERAL[first], NUMERAL[second],
                                          'cmin'), 'wceq')},
                            self.number(second), self.number(first),
                            self.ap('negsubdi2', {'A': NUMERAL[second],
                                                  'B': NUMERAL[first]}))),
            self.ap('negeqd', {'ph': self.under, 'A': other,
                               'B': NUMERAL[second - first]},
                    self.gap_numeral(second, first)),
            op(NUMERAL[first], NUMERAL[second], 'cmin'),
            seq(other, 'cneg'), seq(NUMERAL[second - first], 'cneg'))

    # --- putting one term into a run --------------------------------------

    def combine(self, monomial, first, second):
        """( under -> ( ( c x. M ) + ( d x. M ) ) = ( e x. M ) ).

        `adddir` distributes a sum over a product; read the other way it
        collects two terms that share a monomial, which is the only place
        the coefficients meet."""
        spelt = spell_monomial(monomial)
        c, d = (field.spell_coefficient(first),
                field.spell_coefficient(second))
        total = field.spell_coefficient(first + second)
        gathered = self.ap(
            'eqcomd',
            {'ph': self.under, 'A': op(op(c, d, ADD), spelt, MUL),
             'B': op(op(c, spelt, MUL), op(d, spelt, MUL), ADD)},
            self.ap('syl3anc',
                    {'ph': self.under, 'ps': seq(c, 'cc', 'wcel'),
                     'ch': seq(d, 'cc', 'wcel'),
                     'th': seq(spelt, 'cc', 'wcel'),
                     'ta': seq(op(op(c, d, ADD), spelt, MUL),
                               op(op(c, spelt, MUL), op(d, spelt, MUL), ADD),
                               'wceq')},
                    self.coefficient(first), self.coefficient(second),
                    self.monomial_cc(monomial),
                    self.ap('adddir', {'A': c, 'B': d, 'C': spelt})))
        return self.chain(
            gathered,
            self.ap('oveq1d', {'ph': self.under, 'A': op(c, d, ADD),
                               'B': total, 'C': spelt, 'F': MUL},
                    self.coefficient_sum(first, second)),
            op(op(c, spelt, MUL), op(d, spelt, MUL), ADD),
            op(op(c, d, ADD), spelt, MUL),
            op(total, spelt, MUL))

    def shift(self, items, frm, to):
        """( under -> spell_run(items) = spell_run(moved) ), one term moved.

        Leftward is the direction an appended term travels to reach the
        place its degree puts it; rightward is how a term whose
        coefficient has cancelled reaches the end, where it comes off.
        Each step is one `swap`."""
        start = said = self.spell_run(items)
        proof = None
        for at in (range(frm, to) if to > frm else range(frm - 1, to - 1, -1)):
            step = self.swap(items, at)
            items = [*items[:at], items[at + 1], items[at], *items[at + 2:]]
            after = self.spell_run(items)
            proof = (step if proof is None
                     else self.chain(proof, step, start, said, after))
            said = after
        return items, proof or self.same(start)


    def drop(self, items, at):
        """( under -> spell_run(items) = spell_run(rest) ), a zero term gone.

        A coefficient that has cancelled leaves `( 0 x. M )`, which is
        zero by `mul02` and comes off the end by `addrid`. The term is
        walked to the end first, because that is where it can come off."""
        start = self.spell_run(items)
        items, walked = self.shift(items, at, len(items) - 1)
        run = self.spell_run(items)
        rest = items[:-1]
        zero = self.spell_term(items[-1])
        spelt = spell_monomial(items[-1][0])
        vanishes = self.ap('syl', {'ph': self.under,
                                   'ps': seq(spelt, 'cc', 'wcel'),
                                   'ch': seq(zero, NUMERAL[0], 'wceq')},
                           self.monomial_cc(items[-1][0]),
                           self.ap('mul02', {'A': spelt}))
        if not rest:
            return rest, self.chain(walked, vanishes, start, run, NUMERAL[0])
        keep = self.spell_run(rest)
        comes_off = self.chain(
            self.ap('oveq2d', {'ph': self.under, 'A': zero,
                               'B': NUMERAL[0], 'C': keep, 'F': ADD},
                    vanishes),
            self.ap('syl', {'ph': self.under, 'ps': seq(keep, 'cc', 'wcel'),
                            'ch': seq(op(keep, NUMERAL[0], ADD), keep,
                                      'wceq')},
                    self.run_cc(rest), self.ap('addrid', {'A': keep})),
            run, op(keep, NUMERAL[0], ADD), keep)
        return rest, self.chain(walked, comes_off, start, run, keep)

    def insert(self, items, monomial, weight):
        """( under -> ( spell_run(items) + ( c x. M ) ) = spell_run(out) ).

        One term put where its degree says it goes. If the monomial is
        already there the two coefficients meet and may cancel; otherwise
        the term simply travels left to its place."""
        term = self.spell_term((monomial, weight))
        if not items:
            return [(monomial, weight)], self.ap(
                'syl', {'ph': self.under, 'ps': seq(term, 'cc', 'wcel'),
                        'ch': seq(op(NUMERAL[0], term, ADD), term, 'wceq')},
                self.term_cc(monomial, weight),
                self.ap('addlid', {'A': term}))

        appended = [*items, (monomial, weight)]
        start = self.spell_run(appended)
        here = [m for m, _ in items]
        if monomial in here:
            at = here.index(monomial)
            moved, walked = self.shift(appended, len(items), at + 1)
            total = moved[at][1] + moved[at + 1][1]
            joined = self.gather(moved, at)
            out = [*moved[:at], (monomial, total), *moved[at + 2:]]
            proof = self.chain(walked, joined, start,
                               self.spell_run(moved), self.spell_run(out))
            if total == 0:
                out, gone = self.drop(out, at)
                proof = self.chain(proof, gone, start,
                                   self.spell_run([*moved[:at],
                                                   (monomial, total),
                                                   *moved[at + 2:]]),
                                   self.spell_run(out))
            return out, proof
        goes = sum(1 for m, _ in items if order(m) < order(monomial))
        out, walked = self.shift(appended, len(items), goes)
        return out, walked

    def gather(self, items, at):
        """Two neighbours that share a monomial, collected into one term.

        `addass` exposes them as a pair where they sit at the end of a
        run; where they are the whole of it they are already exposed."""
        head, rest = items[:at], items[at + 2:]
        monomial = items[at][0]
        a, b = self.spell_term(items[at]), self.spell_term(items[at + 1])
        total = self.spell_term((monomial, items[at][1] + items[at + 1][1]))
        collect = self.combine(monomial, items[at][1], items[at + 1][1])
        if not head:
            return self.lift(collect, op(a, b, ADD), total,
                             [self.spell_term(i) for i in rest])
        prefix = self.spell_run(head)
        exposed = self.ap(
            'syl3anc', {'ph': self.under, 'ps': seq(prefix, 'cc', 'wcel'),
                        'ch': seq(a, 'cc', 'wcel'), 'th': seq(b, 'cc', 'wcel'),
                        'ta': seq(op(op(prefix, a, ADD), b, ADD),
                                  op(prefix, op(a, b, ADD), ADD), 'wceq')},
            self.run_cc(head), self.term_cc(*items[at]),
            self.term_cc(*items[at + 1]),
            self.ap('addass', {'A': prefix, 'B': a, 'C': b}))
        step = self.chain(
            exposed,
            self.ap('oveq2d', {'ph': self.under, 'A': op(a, b, ADD),
                               'B': total, 'C': prefix, 'F': ADD}, collect),
            op(op(prefix, a, ADD), b, ADD), op(prefix, op(a, b, ADD), ADD),
            op(prefix, total, ADD))
        return self.lift(step, op(op(prefix, a, ADD), b, ADD),
                         op(prefix, total, ADD),
                         [self.spell_term(i) for i in rest])


    def add(self, left, right):
        """( under -> ( spell_run(left) + spell_run(right) ) = spell_run(sum) ).

        The right-hand run is taken apart from its end, one term at a time,
        and each is put into the left by `insert`. `addass` is what peels
        a term off: the run associates to the left, so its last term is
        already where the law can reach it."""
        start = op(self.spell_run(left), self.spell_run(right), ADD)
        if not right:
            keep = self.spell_run(left)
            return left, self.ap(
                'syl', {'ph': self.under, 'ps': seq(keep, 'cc', 'wcel'),
                        'ch': seq(op(keep, NUMERAL[0], ADD), keep, 'wceq')},
                self.run_cc(left), self.ap('addrid', {'A': keep}))
        if len(right) == 1:
            return self.insert(left, *right[0])

        rest, last = right[:-1], right[-1]
        whole, prefix = self.spell_run(right), self.spell_run(rest)
        held, term = self.spell_run(left), self.spell_term(last)
        peeled = self.ap(
            'eqcomd',
            {'ph': self.under, 'A': op(op(held, prefix, ADD), term, ADD),
             'B': op(held, whole, ADD)},
            self.ap('syl3anc',
                    {'ph': self.under, 'ps': seq(held, 'cc', 'wcel'),
                     'ch': seq(prefix, 'cc', 'wcel'),
                     'th': seq(term, 'cc', 'wcel'),
                     'ta': seq(op(op(held, prefix, ADD), term, ADD),
                               op(held, whole, ADD), 'wceq')},
                    self.run_cc(left), self.run_cc(rest),
                    self.term_cc(*last),
                    self.ap('addass', {'A': held, 'B': prefix, 'C': term})))
        merged, inner = self.add(left, rest)
        carried = self.ap('oveq1d',
                          {'ph': self.under, 'A': op(held, prefix, ADD),
                           'B': self.spell_run(merged), 'C': term,
                           'F': ADD}, inner)
        out, placed = self.insert(merged, *last)
        return out, self.chain(
            self.chain(peeled, carried, start,
                       op(op(held, prefix, ADD), term, ADD),
                       op(self.spell_run(merged), term, ADD)),
            placed, start, op(self.spell_run(merged), term, ADD),
            self.spell_run(out))


    # --- monomials --------------------------------------------------------
    #
    # The same shape as the sum side, over products, and shorter for one
    # reason: a monomial holds only positive powers, so multiplying two of
    # them adds positive numbers and nothing can cancel. There is no
    # counterpart here to `drop`.

    def factor_cc(self, name, power):
        return self.ap('expcld', {'ph': self.under, 'A': name,
                                  'N': NUMERAL[power]},
                       self.atom(name), self.index(power))

    def factors_cc(self, factors):
        if not factors:
            return self.number(1)
        out, running = self.factor_cc(*factors[0]), spell_factor(factors[0])
        for one in factors[1:]:
            out = self.ap('mulcld', {'ph': self.under, 'A': running,
                                     'B': spell_factor(one)},
                          out, self.factor_cc(*one))
            running = op(running, spell_factor(one), MUL)
        return out

    def swap_factors(self, factors, at):
        """`mul32` for `add32`, and `mulcom` where the two are the whole."""
        head = factors[:at]
        a, b = spell_factor(factors[at]), spell_factor(factors[at + 1])
        if head:
            prefix = spell_monomial(tuple(head))
            before, after = op(op(prefix, a, MUL), b, MUL), \
                op(op(prefix, b, MUL), a, MUL)
            step = self.ap('syl3anc',
                           {'ph': self.under, 'ps': seq(prefix, 'cc', 'wcel'),
                            'ch': seq(a, 'cc', 'wcel'),
                            'th': seq(b, 'cc', 'wcel'),
                            'ta': seq(before, after, 'wceq')},
                           self.factors_cc(head), self.factor_cc(*factors[at]),
                           self.factor_cc(*factors[at + 1]),
                           self.ap('mul32', {'A': prefix, 'B': a, 'C': b}))
        else:
            before, after = op(a, b, MUL), op(b, a, MUL)
            step = self.ap('syl2anc',
                           {'ph': self.under, 'ps': seq(a, 'cc', 'wcel'),
                            'ch': seq(b, 'cc', 'wcel'),
                            'th': seq(before, after, 'wceq')},
                           self.factor_cc(*factors[at]),
                           self.factor_cc(*factors[at + 1]),
                           self.ap('mulcom', {'A': a, 'B': b}))
        return self.lift(step, before, after,
                         [spell_factor(f) for f in factors[at + 2:]], MUL)

    def shift_factors(self, factors, frm, to):
        start = said = spell_monomial(tuple(factors))
        proof = None
        for at in range(frm - 1, to - 1, -1):
            step = self.swap_factors(factors, at)
            factors = [*factors[:at], factors[at + 1], factors[at],
                       *factors[at + 2:]]
            after = spell_monomial(tuple(factors))
            proof = (step if proof is None
                     else self.chain(proof, step, start, said, after))
            said = after
        return factors, proof or self.same(start)

    def gather_factors(self, name, first, second):
        """( under -> ( ( x ^ j ) x. ( x ^ k ) ) = ( x ^ ( j + k ) ) ).

        `expadd` read backwards, which is where two powers of one atom
        meet, and the only place the exponents are added."""
        a, b = op(name, NUMERAL[first], EXP), op(name, NUMERAL[second], EXP)
        total = first + second
        if total > 9:
            raise Unhandled(f'{name} to the {total} is past one digit')
        joined = self.ap(
            'eqcomd',
            {'ph': self.under,
             'A': op(name, op(NUMERAL[first], NUMERAL[second], ADD), EXP),
             'B': op(a, b, MUL)},
            self.ap('syl3anc',
                    {'ph': self.under, 'ps': seq(name, 'cc', 'wcel'),
                     'ch': seq(NUMERAL[first], 'cn0', 'wcel'),
                     'th': seq(NUMERAL[second], 'cn0', 'wcel'),
                     'ta': seq(op(name, op(NUMERAL[first], NUMERAL[second],
                                           ADD), EXP), op(a, b, MUL),
                               'wceq')},
                    self.atom(name), self.index(first), self.index(second),
                    self.ap('expadd', {'A': name, 'M': NUMERAL[first],
                                       'N': NUMERAL[second]})))
        return self.chain(
            joined,
            self.ap('oveq2d',
                    {'ph': self.under,
                     'A': op(NUMERAL[first], NUMERAL[second], ADD),
                     'B': NUMERAL[total], 'C': name, 'F': EXP},
                    self.coefficient_sum(Fraction(first), Fraction(second))),
            op(a, b, MUL),
            op(name, op(NUMERAL[first], NUMERAL[second], ADD), EXP),
            op(name, NUMERAL[total], EXP))

    def insert_factor(self, factors, name, power):
        """One factor put where its atom's name says it goes."""
        one = op(name, NUMERAL[power], EXP)
        if not factors:
            return [(name, power)], self.ap(
                'syl', {'ph': self.under, 'ps': seq(one, 'cc', 'wcel'),
                        'ch': seq(op(NUMERAL[1], one, MUL), one, 'wceq')},
                self.factor_cc(name, power),
                self.ap('mullid', {'A': one}))
        appended = [*factors, (name, power)]
        start = spell_monomial(tuple(appended))
        here = [n for n, _ in factors]
        if name in here:
            at = here.index(name)
            moved, walked = self.shift_factors(appended, len(factors), at + 1)
            total = moved[at][1] + moved[at + 1][1]
            out = [*moved[:at], (name, total), *moved[at + 2:]]
            return out, self.chain(
                walked,
                self.spread(moved, at,
                            self.gather_factors(name, moved[at][1],
                                                moved[at + 1][1])),
                start, spell_monomial(tuple(moved)),
                spell_monomial(tuple(out)))
        goes = sum(1 for n, _ in factors if n < name)
        return self.shift_factors(appended, len(factors), goes)

    def spread(self, factors, at, collect):
        """A rewrite of two neighbouring factors, carried to the whole."""
        head, rest = factors[:at], factors[at + 2:]
        a, b = spell_factor(factors[at]), spell_factor(factors[at + 1])
        total = spell_factor((factors[at][0],
                              factors[at][1] + factors[at + 1][1]))
        tail = [spell_factor(f) for f in rest]
        if not head:
            return self.lift(collect, op(a, b, MUL), total, tail, MUL)
        prefix = spell_monomial(tuple(head))
        exposed = self.ap(
            'syl3anc', {'ph': self.under, 'ps': seq(prefix, 'cc', 'wcel'),
                        'ch': seq(a, 'cc', 'wcel'), 'th': seq(b, 'cc', 'wcel'),
                        'ta': seq(op(op(prefix, a, MUL), b, MUL),
                                  op(prefix, op(a, b, MUL), MUL), 'wceq')},
            self.factors_cc(head), self.factor_cc(*factors[at]),
            self.factor_cc(*factors[at + 1]),
            self.ap('mulass', {'A': prefix, 'B': a, 'C': b}))
        step = self.chain(
            exposed,
            self.ap('oveq2d', {'ph': self.under, 'A': op(a, b, MUL),
                               'B': total, 'C': prefix, 'F': MUL}, collect),
            op(op(prefix, a, MUL), b, MUL), op(prefix, op(a, b, MUL), MUL),
            op(prefix, total, MUL))
        return self.lift(step, op(op(prefix, a, MUL), b, MUL),
                         op(prefix, total, MUL), tail, MUL)

    def multiply_monomials(self, left, right):
        """( under -> ( M x. N ) = P ), two monomials merged."""
        start = op(spell_monomial(tuple(left)), spell_monomial(tuple(right)),
                   MUL)
        if not right:
            keep = spell_monomial(tuple(left))
            return left, self.ap(
                'syl', {'ph': self.under, 'ps': seq(keep, 'cc', 'wcel'),
                        'ch': seq(op(keep, NUMERAL[1], MUL), keep, 'wceq')},
                self.factors_cc(left), self.ap('mulrid', {'A': keep}))
        if len(right) == 1:
            return self.insert_factor(left, *right[0])
        rest, last = right[:-1], right[-1]
        whole = spell_monomial(tuple(right))
        prefix = spell_monomial(tuple(rest))
        held, one = spell_monomial(tuple(left)), spell_factor(last)
        peeled = self.ap(
            'eqcomd',
            {'ph': self.under, 'A': op(op(held, prefix, MUL), one, MUL),
             'B': op(held, whole, MUL)},
            self.ap('syl3anc',
                    {'ph': self.under, 'ps': seq(held, 'cc', 'wcel'),
                     'ch': seq(prefix, 'cc', 'wcel'),
                     'th': seq(one, 'cc', 'wcel'),
                     'ta': seq(op(op(held, prefix, MUL), one, MUL),
                               op(held, whole, MUL), 'wceq')},
                    self.factors_cc(left), self.factors_cc(rest),
                    self.factor_cc(*last),
                    self.ap('mulass', {'A': held, 'B': prefix, 'C': one})))
        merged, inner = self.multiply_monomials(left, rest)
        carried = self.ap('oveq1d',
                          {'ph': self.under, 'A': op(held, prefix, MUL),
                           'B': spell_monomial(tuple(merged)), 'C': one,
                           'F': MUL}, inner)
        out, placed = self.insert_factor(merged, *last)
        return out, self.chain(
            self.chain(peeled, carried, start,
                       op(op(held, prefix, MUL), one, MUL),
                       op(spell_monomial(tuple(merged)), one, MUL)),
            placed, start, op(spell_monomial(tuple(merged)), one, MUL),
            spell_monomial(tuple(out)))


    # --- multiplying ------------------------------------------------------

    def positive_product(self, first, second):
        """( under -> ( a x. b ) = c ) for two whole numbers."""
        a, b = NUMERAL[first], NUMERAL[second]
        claim = seq(op(a, b, MUL), NUMERAL[first * second], 'wceq')
        if first == 0:
            return self.a1i(claim, self.mp(seq(b, 'cc', 'wcel'), claim,
                                           self.complex_label(second),
                                           self.ap('mul02', {'A': b})))
        if second == 0:
            return self.a1i(claim, self.mp(seq(a, 'cc', 'wcel'), claim,
                                           self.complex_label(first),
                                           self.ap('mul01', {'A': a})))
        if first == 1:
            return self.a1i(claim, self.mp(seq(b, 'cc', 'wcel'), claim,
                                           self.complex_label(second),
                                           self.ap('mullid', {'A': b})))
        if second == 1:
            return self.a1i(claim, self.mp(seq(a, 'cc', 'wcel'), claim,
                                           self.complex_label(first),
                                           self.ap('mulrid', {'A': a})))
        return self.a1i(claim, f'{first}t{second}e{first * second}')

    def coefficient_product(self, first, second):
        """( under -> ( c x. d ) = e ), the coefficients as `spell` has them.

        Signs come off first — `mulneg1`, `mulneg2` and `mul2neg` say where
        the minus goes — and what is left is two whole numbers, which
        set.mm names a lemma for."""
        total = first * second
        said = field.spell_coefficient(total)
        c = field.spell_coefficient(first)
        d = field.spell_coefficient(second)
        if said is None or c is None or d is None:
            raise Unhandled(f'{first} x. {second} is past one digit')
        a, b = first.numerator, second.numerator
        if a >= 0 and b >= 0:
            return self.positive_product(a, b)
        size = self.positive_product(abs(a), abs(b))
        whole = op(NUMERAL[abs(a)], NUMERAL[abs(b)], MUL)
        if a < 0 and b < 0:
            return self.chain(
                self.pair('mul2neg', NUMERAL[abs(a)], NUMERAL[abs(b)],
                          op(c, d, MUL), whole),
                size, op(c, d, MUL), whole, said)
        label = 'mulneg1' if a < 0 else 'mulneg2'
        return self.chain(
            self.pair(label, NUMERAL[abs(a)], NUMERAL[abs(b)],
                      op(c, d, MUL), seq(whole, 'cneg')),
            self.ap('negeqd', {'ph': self.under, 'A': whole,
                               'B': NUMERAL[abs(a * b)]}, size),
            op(c, d, MUL), seq(whole, 'cneg'), said)

    def pair(self, label, left, right, before, after):
        """A two-argument law of ℂ, applied to two numerals."""
        return self.ap('syl2anc',
                       {'ph': self.under, 'ps': seq(left, 'cc', 'wcel'),
                        'ch': seq(right, 'cc', 'wcel'),
                        'th': seq(before, after, 'wceq')},
                       self.number(int(left_value(left))),
                       self.number(int(left_value(right))),
                       self.ap(label, {'A': left, 'B': right}))

    def term_times_term(self, one, two):
        """( under -> ( ( c x. M ) x. ( d x. N ) ) = ( e x. P ) ).

        `mul4` puts the two coefficients together and the two monomials
        together, and then each side is its own problem."""
        (first, weight), (second, other) = one, two
        c = field.spell_coefficient(weight)
        d = field.spell_coefficient(other)
        m, n = spell_monomial(first), spell_monomial(second)
        a, b = self.spell_term(one), self.spell_term(two)
        regrouped = self.ap(
            'syl', {'ph': self.under,
                    'ps': seq(seq(seq(c, 'cc', 'wcel'), seq(m, 'cc', 'wcel'),
                                  'wa'),
                              seq(seq(d, 'cc', 'wcel'), seq(n, 'cc', 'wcel'),
                                  'wa'), 'wa'),
                    'ch': seq(op(a, b, MUL),
                              op(op(c, d, MUL), op(m, n, MUL), MUL), 'wceq')},
            self.ap('jca', {'ph': self.under,
                            'ps': seq(seq(c, 'cc', 'wcel'),
                                      seq(m, 'cc', 'wcel'), 'wa'),
                            'ch': seq(seq(d, 'cc', 'wcel'),
                                      seq(n, 'cc', 'wcel'), 'wa')},
                   self.ap('jca', {'ph': self.under,
                                   'ps': seq(c, 'cc', 'wcel'),
                                   'ch': seq(m, 'cc', 'wcel')},
                           self.coefficient(weight),
                           self.monomial_cc(first)),
                   self.ap('jca', {'ph': self.under,
                                   'ps': seq(d, 'cc', 'wcel'),
                                   'ch': seq(n, 'cc', 'wcel')},
                           self.coefficient(other),
                           self.monomial_cc(second))),
            self.ap('mul4', {'A': c, 'B': m, 'C': d, 'D': n}))
        merged, monomial = self.multiply_monomials(list(first), list(second))
        total = weight * other
        out = (tuple(merged), total)
        return out, self.chain(
            regrouped,
            self.ap('oveq12d',
                    {'ph': self.under, 'A': op(c, d, MUL),
                     'B': field.spell_coefficient(total),
                     'C': op(m, n, MUL),
                     'D': spell_monomial(tuple(merged)), 'F': MUL},
                    self.coefficient_product(weight, other), monomial),
            op(a, b, MUL), op(op(c, d, MUL), op(m, n, MUL), MUL),
            self.spell_term(out))


    def term_times_run(self, one, right):
        """( under -> ( t x. spell_run(right) ) = spell_run(product) ).

        `adddi` takes the right-hand run apart from its end, one term at a
        time, and each product of two terms is `term_times_term`."""
        term = self.spell_term(one)
        start = op(term, self.spell_run(right), MUL)
        if not right:
            return [], self.ap(
                'syl', {'ph': self.under, 'ps': seq(term, 'cc', 'wcel'),
                        'ch': seq(op(term, NUMERAL[0], MUL), NUMERAL[0],
                                  'wceq')},
                self.term_cc(*one), self.ap('mul01', {'A': term}))
        if len(right) == 1:
            out, proof = self.term_times_term(one, right[0])
            return [out], proof
        rest, last = right[:-1], right[-1]
        prefix, tail = self.spell_run(rest), self.spell_term(last)
        spread = self.ap(
            'syl3anc',
            {'ph': self.under, 'ps': seq(term, 'cc', 'wcel'),
             'ch': seq(prefix, 'cc', 'wcel'), 'th': seq(tail, 'cc', 'wcel'),
             'ta': seq(start, op(op(term, prefix, MUL),
                                 op(term, tail, MUL), ADD), 'wceq')},
            self.term_cc(*one), self.run_cc(rest), self.term_cc(*last),
            self.ap('adddi', {'A': term, 'B': prefix, 'C': tail}))
        inner, first = self.term_times_run(one, rest)
        single, second = self.term_times_term(one, last)
        both = op(self.spell_run(inner), self.spell_term(single), ADD)
        lined = self.chain(
            spread,
            self.ap('oveq12d',
                    {'ph': self.under, 'A': op(term, prefix, MUL),
                     'B': self.spell_run(inner), 'C': op(term, tail, MUL),
                     'D': self.spell_term(single), 'F': ADD}, first, second),
            start, op(op(term, prefix, MUL), op(term, tail, MUL), ADD), both)
        out, placed = self.insert(inner, *single)
        return out, self.chain(lined, placed, start, both,
                               self.spell_run(out))

    def multiply(self, left, right):
        """( under -> ( spell_run(left) x. spell_run(right) ) = the product ).

        `adddir` takes the left-hand run apart, and what each of its terms
        does to the whole right-hand run is `term_times_run`. The pieces
        are then added, which is what `add` is for."""
        start = op(self.spell_run(left), self.spell_run(right), MUL)
        if not left:
            keep = self.spell_run(right)
            return [], self.ap(
                'syl', {'ph': self.under, 'ps': seq(keep, 'cc', 'wcel'),
                        'ch': seq(op(NUMERAL[0], keep, MUL), NUMERAL[0],
                                  'wceq')},
                self.run_cc(right), self.ap('mul02', {'A': keep}))
        if len(left) == 1:
            return self.term_times_run(left[0], right)
        rest, last = left[:-1], left[-1]
        prefix, tail = self.spell_run(rest), self.spell_term(last)
        whole = self.spell_run(right)
        spread = self.ap(
            'syl3anc',
            {'ph': self.under, 'ps': seq(prefix, 'cc', 'wcel'),
             'ch': seq(tail, 'cc', 'wcel'), 'th': seq(whole, 'cc', 'wcel'),
             'ta': seq(start, op(op(prefix, whole, MUL),
                                 op(tail, whole, MUL), ADD), 'wceq')},
            self.run_cc(rest), self.term_cc(*last), self.run_cc(right),
            self.ap('adddir', {'A': prefix, 'B': tail, 'C': whole}))
        inner, first = self.multiply(rest, right)
        outer, second = self.term_times_run(last, right)
        both = op(self.spell_run(inner), self.spell_run(outer), ADD)
        lined = self.chain(
            spread,
            self.ap('oveq12d',
                    {'ph': self.under, 'A': op(prefix, whole, MUL),
                     'B': self.spell_run(inner), 'C': op(tail, whole, MUL),
                     'D': self.spell_run(outer), 'F': ADD}, first, second),
            start, op(op(prefix, whole, MUL), op(tail, whole, MUL), ADD),
            both)
        out, joined = self.add(inner, outer)
        return out, self.chain(lined, joined, start, both,
                               self.spell_run(out))


    def power(self, items, times):
        """( under -> ( spell_run(items) ^ k ) = spell_run(the power) ).

        `expp1` peels one factor off, and it states the exponent as
        `N + 1`, so the numeral is rewritten that way round first."""
        run = self.spell_run(items)
        start = op(run, NUMERAL[times], EXP)
        if times == 0:
            return [((), Fraction(1))], self.chain(
                self.ap('syl', {'ph': self.under,
                                'ps': seq(run, 'cc', 'wcel'),
                                'ch': seq(start, NUMERAL[1], 'wceq')},
                        self.run_cc(items), self.ap('exp0', {'A': run})),
                self.one_as_term(), start, NUMERAL[1],
                self.spell_term(((), Fraction(1))))
        if times == 1:
            return items, self.ap(
                'syl', {'ph': self.under, 'ps': seq(run, 'cc', 'wcel'),
                        'ch': seq(start, run, 'wceq')},
                self.run_cc(items), self.ap('exp1', {'A': run}))
        below = NUMERAL[times - 1]
        stepped = self.chain(
            self.ap('oveq2d', {'ph': self.under, 'A': NUMERAL[times],
                               'B': op(below, NUMERAL[1], ADD), 'C': run,
                               'F': EXP},
                    self.ap('eqcomd',
                            {'ph': self.under,
                             'A': op(below, NUMERAL[1], ADD),
                             'B': NUMERAL[times]},
                            self.coefficient_sum(Fraction(times - 1),
                                                 Fraction(1)))),
            self.ap('syl2anc',
                    {'ph': self.under, 'ps': seq(run, 'cc', 'wcel'),
                     'ch': seq(below, 'cn0', 'wcel'),
                     'th': seq(op(run, op(below, NUMERAL[1], ADD), EXP),
                               op(op(run, below, EXP), run, MUL), 'wceq')},
                    self.run_cc(items), self.index(times - 1),
                    self.ap('expp1', {'A': run, 'N': below})),
            start, op(run, op(below, NUMERAL[1], ADD), EXP),
            op(op(run, below, EXP), run, MUL))
        inner, smaller = self.power(items, times - 1)
        carried = self.ap('oveq1d',
                          {'ph': self.under, 'A': op(run, below, EXP),
                           'B': self.spell_run(inner), 'C': run, 'F': MUL},
                          smaller)
        out, product = self.multiply(inner, items)
        return out, self.chain(
            self.chain(stepped, carried, start,
                       op(op(run, below, EXP), run, MUL),
                       op(self.spell_run(inner), run, MUL)),
            product, start, op(self.spell_run(inner), run, MUL),
            self.spell_run(out))

    def one_as_term(self):
        """( under -> 1 = ( 1 x. 1 ) ), the canonical form of one."""
        return self.ap('eqcomd',
                       {'ph': self.under,
                        'A': op(NUMERAL[1], NUMERAL[1], MUL),
                        'B': NUMERAL[1]},
                       self.positive_product(1, 1))

    # --- the driver -------------------------------------------------------

    def normalize(self, term, labels):
        """(items, ( under -> term = spell_run(items) )).

        Recursion on the term, not a search: at each node the children are
        already canonical and what remains is one of the operations above.
        A subterm this does not recognise is an atom, and the caller is
        asked once for its membership."""
        said = term.rpn(labels)
        if term.variable is None and term.label in field.DIGITS:
            value = Fraction(field.DIGITS[term.label])
            if value == 0:
                # The empty run, not a term of weight zero: a canonical
                # form holds no such term, and one left in it would be
                # carried through every sum it took part in.
                return [], self.same(NUMERAL[0])
            if value == 1:
                return [((), value)], self.one_as_term()
            return [((), value)], self.ap(
                'eqcomd', {'ph': self.under,
                           'A': op(NUMERAL[int(value)], NUMERAL[1], MUL),
                           'B': NUMERAL[int(value)]},
                self.positive_product(int(value), 1))
        if term.variable is None and term.label == 'cneg' \
                and len(term.children) == 1:
            items, proof = self.normalize(term.children[0], labels)
            return self.negated(term.children[0].rpn(labels), items, proof,
                                said)
        if term.variable is None and term.label == 'co' \
                and len(term.children) == 3:
            how = term.children[2].rpn(labels)
            left, right = term.children[0], term.children[1]
            if how in (field.ADD, field.SUB, field.MUL):
                return self.binary(how, left, right, labels, said)
            if how == field.EXP:
                times = field.numeral(right, labels)
                if times is None or not 0 <= times <= 9:
                    raise Unhandled(f'{said} has no numeral exponent')
                inner, proof = self.normalize(left, labels)
                out, raised = self.power(inner, times)
                return out, self.chain(
                    self.ap('oveq1d',
                            {'ph': self.under, 'A': left.rpn(labels),
                             'B': self.spell_run(inner),
                             'C': NUMERAL[times], 'F': EXP}, proof),
                    raised, said,
                    op(self.spell_run(inner), NUMERAL[times], EXP),
                    self.spell_run(out))
            if how == field.DIV:
                raise Unhandled(f'{said} divides, which is cross-multiplied')
        return self.as_atom(said)

    def as_atom(self, said):
        """A subterm nothing above recognises, as `( 1 x. ( t ^ 1 ) )`."""
        raised = op(said, NUMERAL[1], EXP)
        return [(((said, 1),), Fraction(1))], self.chain(
            self.ap('eqcomd', {'ph': self.under, 'A': raised, 'B': said},
                    self.ap('syl', {'ph': self.under,
                                    'ps': seq(said, 'cc', 'wcel'),
                                    'ch': seq(raised, said, 'wceq')},
                            self.atom(said), self.ap('exp1', {'A': said}))),
            self.ap('eqcomd',
                    {'ph': self.under, 'A': op(NUMERAL[1], raised, MUL),
                     'B': raised},
                    self.ap('syl', {'ph': self.under,
                                    'ps': seq(raised, 'cc', 'wcel'),
                                    'ch': seq(op(NUMERAL[1], raised, MUL),
                                              raised, 'wceq')},
                            self.factor_cc(said, 1),
                            self.ap('mullid', {'A': raised}))),
            said, raised, op(NUMERAL[1], raised, MUL))

    def negated(self, inner, items, proof, said):
        """-u X, taken as ( -u 1 ) x. X so that `multiply` does the work.

        The minus one has to be written the way a canonical form writes a
        constant, `( -u 1 x. 1 )`, before `multiply` will take it, which
        `mulrid` supplies."""
        run = self.spell_run(items)
        minus, bare = [((), Fraction(-1))], seq(NUMERAL[1], 'cneg')
        unit = self.spell_run(minus)
        inner_cc = self.ap('eqeltrd', {'ph': self.under, 'A': inner,
                                       'B': run, 'C': 'cc'},
                           proof, self.run_cc(items))
        becomes = self.ap(
            'eqcomd', {'ph': self.under, 'A': op(bare, inner, MUL),
                       'B': said},
            self.ap('syl', {'ph': self.under,
                            'ps': seq(inner, 'cc', 'wcel'),
                            'ch': seq(op(bare, inner, MUL), said, 'wceq')},
                    inner_cc, self.ap('mulm1', {'A': inner})))
        inside = self.ap('oveq2d', {'ph': self.under, 'A': inner, 'B': run,
                                    'C': bare, 'F': MUL}, proof)
        spelt = self.ap(
            'oveq1d', {'ph': self.under, 'A': bare, 'B': unit, 'C': run,
                       'F': MUL},
            self.ap('eqcomd', {'ph': self.under, 'A': unit, 'B': bare},
                    self.ap('syl', {'ph': self.under,
                                    'ps': seq(bare, 'cc', 'wcel'),
                                    'ch': seq(unit, bare, 'wceq')},
                            self.coefficient(Fraction(-1)),
                            self.ap('mulrid', {'A': bare}))))
        out, product = self.multiply(minus, items)
        return out, self.chain(
            self.chain(
                self.chain(becomes, inside, said, op(bare, inner, MUL),
                           op(bare, run, MUL)),
                spelt, said, op(bare, run, MUL), op(unit, run, MUL)),
            product, said, op(unit, run, MUL), self.spell_run(out))

    def subtracted(self, la, lb, first, one, second, two, said):
        """X - Y, turned into X + -u Y, which the sum side already does.

        `negsub` states the two as equal one way round, so it is read
        backwards; the negation is then the case already written."""
        a_cc = self.ap('eqeltrd', {'ph': self.under, 'A': la,
                                   'B': self.spell_run(first), 'C': 'cc'},
                       one, self.run_cc(first))
        b_cc = self.ap('eqeltrd', {'ph': self.under, 'A': lb,
                                   'B': self.spell_run(second), 'C': 'cc'},
                       two, self.run_cc(second))
        minus = seq(lb, 'cneg')
        plus = op(la, minus, ADD)
        turned = self.ap(
            'eqcomd', {'ph': self.under, 'A': plus, 'B': said},
            self.ap('syl2anc', {'ph': self.under,
                                'ps': seq(la, 'cc', 'wcel'),
                                'ch': seq(lb, 'cc', 'wcel'),
                                'th': seq(plus, said, 'wceq')},
                    a_cc, b_cc, self.ap('negsub', {'A': la, 'B': lb})))
        negated, backwards = self.negated(lb, second, two, minus)
        joined = self.ap('oveq12d',
                         {'ph': self.under, 'A': la,
                          'B': self.spell_run(first), 'C': minus,
                          'D': self.spell_run(negated), 'F': ADD},
                         one, backwards)
        out, combined = self.add(first, negated)
        middle = op(self.spell_run(first), self.spell_run(negated), ADD)
        return out, self.chain(
            self.chain(turned, joined, said, plus, middle),
            combined, said, middle, self.spell_run(out))

    def binary(self, how, left, right, labels, said):
        """`+`, `-` or `x.` with both sides taken to canonical form first."""
        first, one = self.normalize(left, labels)
        second, two = self.normalize(right, labels)
        if how == field.SUB:
            return self.subtracted(left.rpn(labels), right.rpn(labels),
                                   first, one, second, two, said)
        what = ADD if how == field.ADD else MUL
        joined = self.ap('oveq12d',
                         {'ph': self.under, 'A': left.rpn(labels),
                          'B': self.spell_run(first),
                          'C': right.rpn(labels),
                          'D': self.spell_run(second), 'F': what}, one, two)
        out, combined = (self.add(first, second) if how == field.ADD
                         else self.multiply(first, second))
        middle = op(self.spell_run(first), self.spell_run(second), what)
        return out, self.chain(joined, combined, said, middle,
                               self.spell_run(out))


    # --- quotients ---------------------------------------------------------
    #
    # A canonical form with a denominator is a pair rather than a polynomial
    # with fractions in it. Everything above keeps working on the numerator,
    # because its coefficients stay whole; what is added here is bookkeeping
    # on a second polynomial, and the four laws that say how the two travel
    # through a sum, a product, a division and a power.

    def spell_quotient(self, over, under):
        """The canonical term for a pair, or for a numerator on its own."""
        if under is None:
            return self.spell_run(over)
        return op(self.spell_run(over), self.spell_run(under), DIV)

    def denominator(self, under):
        """( under -> d e. CC ) and ( under -> d =/= 0 ) for a denominator.

        A denominator that is a number says for itself that it is not
        zero, since the canonical form of a constant is `( n x. 1 )` and
        the scope knows only about the `n`."""
        said = self.spell_run(under)
        if len(under) == 1:
            monomial, weight = under[0]
            if weight.denominator == 1 and weight.numerator != 0:
                return self.run_cc(under), self.term_apart(monomial, weight)
        if self.apart is None:
            raise Unhandled('nothing can say a denominator is not zero')
        return self.run_cc(under), self.apart(said)

    def term_apart(self, monomial, weight):
        """( under -> ( c x. M ) =/= 0 ), for a denominator of one term.

        The scope knows about the atoms; the canonical form it is asked
        about is `( c x. ( x ^ k ) )`, which the scope has never heard of.
        A product is not zero when neither side is, and a power is not
        when what it raises is not, so the whole of it comes off the
        atoms the scope does know."""
        digit = field.spell_coefficient(weight)
        whole = abs(weight.numerator)
        nonzero = self.a1i(seq(NUMERAL[whole], 'cc0', 'wne'),
                           self.apart_label(whole))
        if weight.numerator < 0:
            nonzero = self.ap('negne0d', {'ph': self.under,
                                          'A': NUMERAL[whole]},
                              self.number(whole), nonzero)
        spelt = spell_monomial(monomial)
        return self.ap('mulne0d', {'ph': self.under, 'A': digit,
                                   'B': spelt},
                       self.coefficient(weight), self.monomial_cc(monomial),
                       nonzero, self.monomial_apart(monomial))

    def monomial_apart(self, monomial):
        """( under -> M =/= 0 ), the empty one being one."""
        if not monomial:
            return self.a1i(seq(NUMERAL[1], 'cc0', 'wne'),
                            self.apart_label(1))
        if self.apart is None:
            raise Unhandled('nothing can say an atom is not zero')
        out, running, held = None, None, None
        for name, power in monomial:
            spelt = op(name, NUMERAL[power], EXP)
            one = self.ap('expne0d', {'ph': self.under, 'A': name,
                                      'N': NUMERAL[power]},
                          self.atom(name), self.apart(name),
                          self.whole_index(power))
            mine = self.factor_cc(name, power)
            if out is None:
                out, running, held = one, spelt, mine
            else:
                out = self.ap('mulne0d', {'ph': self.under, 'A': running,
                                          'B': spelt},
                              held, mine, out, one)
                held = self.ap('mulcld', {'ph': self.under, 'A': running,
                                          'B': spelt}, held, mine)
                running = op(running, spelt, MUL)
        return out

    def whole_index(self, power):
        """( under -> k e. ZZ ), which `expne0d` asks for."""
        return self.a1i(seq(NUMERAL[power], 'cz', 'wcel'), f'{power}z')

    def as_quotient(self, over, under, proof, said):
        """A numerator on its own, given the denominator of one it hides.

        `div1` says a term over one is the term, so it is what promotes a
        polynomial into the pair the laws below want."""
        if under is not None:
            return over, under, proof
        one = [((), Fraction(1))]
        run, unit = self.spell_run(over), self.spell_run(one)
        # `div1` says a term over one is the term, and one in canonical
        # form is `( 1 x. 1 )`, so the denominator is tidied to that first.
        back = self.chain(
            self.ap('oveq2d', {'ph': self.under, 'A': unit,
                               'B': NUMERAL[1], 'C': run, 'F': DIV},
                    self.ap('eqcomd', {'ph': self.under, 'A': NUMERAL[1],
                                       'B': unit}, self.one_as_term())),
            self.ap('syl', {'ph': self.under, 'ps': seq(run, 'cc', 'wcel'),
                            'ch': seq(op(run, NUMERAL[1], DIV), run,
                                      'wceq')},
                    self.run_cc(over), self.ap('div1', {'A': run})),
            op(run, unit, DIV), op(run, NUMERAL[1], DIV), run)
        return over, one, self.chain(
            proof,
            self.ap('eqcomd', {'ph': self.under, 'A': op(run, unit, DIV),
                               'B': run}, back),
            said, run, op(run, unit, DIV))

    def normalize_quotient(self, term, labels):
        """(over, under, ( under -> term = over / under )).

        `under` is None where the term divides nothing, and the proof is
        then of the numerator alone: a term that divides nothing must not
        be made to carry a denominator of one, or every caller's output
        would change."""
        said = term.rpn(labels)
        if not divides(term, labels):
            items, proof = self.normalize(term, labels)
            return items, None, proof
        if term.variable is None and term.label == 'co' \
                and len(term.children) == 3:
            how = term.children[2].rpn(labels)
            left, right = term.children[0], term.children[1]
            if how == field.DIV:
                return self.quotient_of(left, right, labels, said)
            if how in (field.ADD, field.MUL):
                return self.quotient_joined(how, left, right, labels, said)
            if how == field.EXP:
                return self.quotient_raised(left, right, labels, said)
        raise Unhandled(f'{said} divides somewhere this does not reach')

    def quotient_of(self, left, right, labels, said):
        """`a / b`, where what is below may divide as well.

        `divdiv1` is what folds a division under a division into one."""
        over, under, first = self.normalize_quotient(left, labels)
        below, beneath, second = self.normalize_quotient(right, labels)
        if beneath is not None:
            raise Unhandled(f'{said} divides by something that divides')
        joined = self.ap('oveq12d',
                         {'ph': self.under, 'A': left.rpn(labels),
                          'B': self.spell_quotient(over, under),
                          'C': right.rpn(labels),
                          'D': self.spell_run(below), 'F': DIV},
                         first, second)
        if under is None:
            return over, below, joined
        # ( A / B ) / C is A / ( B x. C ), and the new denominator is then
        # the two of them multiplied out.
        top, bottom = self.spell_run(over), self.spell_run(under)
        outer = self.spell_run(below)
        folded = self.ap(
            'syl3anc',
            {'ph': self.under, 'ps': seq(top, 'cc', 'wcel'),
             'ch': seq(seq(bottom, 'cc', 'wcel'), seq(bottom, 'cc0', 'wne'),
                       'wa'),
             'th': seq(seq(outer, 'cc', 'wcel'), seq(outer, 'cc0', 'wne'),
                       'wa'),
             'ta': seq(op(op(top, bottom, DIV), outer, DIV),
                       op(top, op(bottom, outer, MUL), DIV), 'wceq')},
            self.run_cc(over), self.pair_of(under), self.pair_of(below),
            self.ap('divdiv1', {'A': top, 'B': bottom, 'C': outer}))
        made, product = self.multiply(under, below)
        return over, made, self.chain(
            self.chain(joined, folded,
                       said, op(op(top, bottom, DIV), outer, DIV),
                       op(top, op(bottom, outer, MUL), DIV)),
            self.ap('oveq2d', {'ph': self.under, 'A': op(bottom, outer, MUL),
                               'B': self.spell_run(made), 'C': top,
                               'F': DIV}, product),
            said, op(top, op(bottom, outer, MUL), DIV),
            op(top, self.spell_run(made), DIV))

    def pair_of(self, under):
        """( under -> ( d e. CC /\\ d =/= 0 ) ), which every law wants."""
        said = self.spell_run(under)
        held, nonzero = self.denominator(under)
        return self.ap('jca', {'ph': self.under,
                               'ps': seq(said, 'cc', 'wcel'),
                               'ch': seq(said, 'cc0', 'wne')},
                       held, nonzero)

    def quotient_joined(self, how, left, right, labels, said):
        """`a + b` or `a x. b` where one of them divides.

        `divadddiv` and `divmuldiv` say what the pair becomes, and the
        numerator and denominator they land on are then multiplied out by
        the operations above."""
        over, under, first = self.as_quotient(
            *self.normalize_quotient(left, labels), left.rpn(labels))
        below, beneath, second = self.as_quotient(
            *self.normalize_quotient(right, labels), right.rpn(labels))
        a, b = self.spell_run(over), self.spell_run(under)
        c, d = self.spell_run(below), self.spell_run(beneath)
        joined = self.ap('oveq12d',
                         {'ph': self.under, 'A': left.rpn(labels),
                          'B': op(a, b, DIV), 'C': right.rpn(labels),
                          'D': op(c, d, DIV),
                          'F': ADD if how == field.ADD else MUL},
                         first, second)
        if how == field.ADD:
            # The numerator a sum lands on is two products added, so each
            # is multiplied out and then the two of them joined.
            label, top = 'divadddiv', op(op(a, d, MUL), op(c, b, MUL), ADD)
            first_items, one = self.multiply(over, beneath)
            second_items, two = self.multiply(below, under)
            made, together = self.add(first_items, second_items)
            middle = op(self.spell_run(first_items),
                        self.spell_run(second_items), ADD)
            numerator = self.chain(
                self.ap('oveq12d',
                        {'ph': self.under, 'A': op(a, d, MUL),
                         'B': self.spell_run(first_items),
                         'C': op(c, b, MUL),
                         'D': self.spell_run(second_items), 'F': ADD},
                        one, two),
                together, top, middle, self.spell_run(made))
        else:
            label, top = 'divmuldiv', op(a, c, MUL)
            made, numerator = self.multiply(over, below)
        bottom = op(b, d, MUL)
        spread = self.ap(
            'syl2anc',
            {'ph': self.under,
             'ps': seq(seq(a, 'cc', 'wcel'), seq(c, 'cc', 'wcel'), 'wa'),
             'ch': seq(seq(seq(b, 'cc', 'wcel'), seq(b, 'cc0', 'wne'), 'wa'),
                       seq(seq(d, 'cc', 'wcel'), seq(d, 'cc0', 'wne'), 'wa'),
                       'wa'),
             'th': seq(op(op(a, b, DIV), op(c, d, DIV),
                          ADD if how == field.ADD else MUL),
                       op(top, bottom, DIV), 'wceq')},
            self.ap('jca', {'ph': self.under, 'ps': seq(a, 'cc', 'wcel'),
                            'ch': seq(c, 'cc', 'wcel')},
                    self.run_cc(over), self.run_cc(below)),
            self.ap('jca', {'ph': self.under,
                            'ps': seq(seq(b, 'cc', 'wcel'),
                                      seq(b, 'cc0', 'wne'), 'wa'),
                            'ch': seq(seq(d, 'cc', 'wcel'),
                                      seq(d, 'cc0', 'wne'), 'wa')},
                    self.pair_of(under), self.pair_of(beneath)),
            self.ap(label, {'A': a, 'B': c, 'C': b, 'D': d}))
        low, denominator = self.multiply(under, beneath)
        return made, low, self.chain(
            self.chain(joined, spread, said,
                       op(op(a, b, DIV), op(c, d, DIV),
                          ADD if how == field.ADD else MUL),
                       op(top, bottom, DIV)),
            self.ap('oveq12d',
                    {'ph': self.under, 'A': top,
                     'B': self.spell_run(made), 'C': bottom,
                     'D': self.spell_run(low), 'F': DIV},
                    numerator, denominator),
            said, op(top, bottom, DIV),
            op(self.spell_run(made), self.spell_run(low), DIV))

    def quotient_raised(self, left, right, labels, said):
        """`( a / b ) ^ k`, which `expdiv` takes apart."""
        times = field.numeral(right, labels)
        if times is None or not 0 <= times <= 9:
            raise Unhandled(f'{said} has no numeral exponent')
        over, under, first = self.as_quotient(
            *self.normalize_quotient(left, labels), left.rpn(labels))
        a, b = self.spell_run(over), self.spell_run(under)
        joined = self.ap('oveq1d',
                         {'ph': self.under, 'A': left.rpn(labels),
                          'B': op(a, b, DIV), 'C': NUMERAL[times],
                          'F': EXP}, first)
        spread = self.ap(
            'syl3anc',
            {'ph': self.under, 'ps': seq(a, 'cc', 'wcel'),
             'ch': seq(seq(b, 'cc', 'wcel'), seq(b, 'cc0', 'wne'), 'wa'),
             'th': seq(NUMERAL[times], 'cn0', 'wcel'),
             'ta': seq(op(op(a, b, DIV), NUMERAL[times], EXP),
                       op(op(a, NUMERAL[times], EXP),
                          op(b, NUMERAL[times], EXP), DIV), 'wceq')},
            self.run_cc(over), self.pair_of(under), self.index(times),
            self.ap('expdiv', {'A': a, 'B': b, 'N': NUMERAL[times]}))
        made, numerator = self.power(over, times)
        low, denominator = self.power(under, times)
        return made, low, self.chain(
            self.chain(joined, spread, said,
                       op(op(a, b, DIV), NUMERAL[times], EXP),
                       op(op(a, NUMERAL[times], EXP),
                          op(b, NUMERAL[times], EXP), DIV)),
            self.ap('oveq12d',
                    {'ph': self.under, 'A': op(a, NUMERAL[times], EXP),
                     'B': self.spell_run(made),
                     'C': op(b, NUMERAL[times], EXP),
                     'D': self.spell_run(low), 'F': DIV},
                    numerator, denominator),
            said,
            op(op(a, NUMERAL[times], EXP), op(b, NUMERAL[times], EXP), DIV),
            op(self.spell_run(made), self.spell_run(low), DIV))


def divides(term, labels):
    """Whether a division appears anywhere in this term."""
    if term.variable is not None:
        return False
    if term.label == 'co' and len(term.children) == 3 \
            and term.children[2].rpn(labels) == field.DIV:
        return True
    return any(divides(one, labels) for one in term.children)


def left_value(numeral):
    """The number a single-digit numeral label stands for."""
    return field.DIGITS[numeral]


def spell_factor(factor):
    """One factor of a monomial, always `( x ^ k )`."""
    name, power = factor
    return op(name, NUMERAL[power], EXP)


def terms_of(poly):
    """A polynomial as its terms in canonical order."""
    return [(m, poly.terms[m]) for m in sorted(poly.terms, key=order)]


class Unhandled(Exception):
    """A form this emitter cannot build a proof for.

    The step is refused rather than guessed at, and `elaborate.py` takes it
    as stated instead, which is what it did before this module existed."""
