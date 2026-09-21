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
import field
from field import NUMERAL, order, spell_monomial

ADD, MUL, EXP = 'caddc', 'cmul', 'cexp'


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

    def __init__(self, sigs, under, atom):
        self.sigs = sigs
        self.under = under
        self.atom = atom                  # rpn -> ( under -> rpn e. CC )
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

    def number(self, value):
        """( under -> n e. CC ) for a whole number the kernel spells."""
        label = 'ax-1cn' if value == 1 else f'{value}cn'
        return self.ap('a1i', {'ph': seq(NUMERAL[value], 'cc', 'wcel'),
                               'ps': self.under}, label)

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

    def lift(self, proof, left, right, tail):
        """Carry an equality of a prefix out to the whole sum.

        A canonical form associates to the left, so a rewrite of the first
        k terms sits under one `oveq1d` for each term after them."""
        for one in tail:
            proof = self.ap('oveq1d',
                            {'ph': self.under, 'A': left, 'B': right,
                             'C': one, 'F': ADD}, proof)
            left, right = op(left, one, ADD), op(right, one, ADD)
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
        if a == -b and a > 0:
            return self.ap('negidd', {'ph': self.under, 'A': NUMERAL[a]},
                           self.number(a))
        if a < 0 or b < 0:
            raise Unhandled(f'{first} + {second} needs signed arithmetic')
        if a == 0:
            return self.a1i(claim, self.mp(seq(d, 'cc', 'wcel'), claim,
                                           f'{b}cn',
                                           self.ap('addlid', {'A': d})))
        if b == 0:
            return self.a1i(claim, self.mp(seq(c, 'cc', 'wcel'), claim,
                                           f'{a}cn',
                                           self.ap('addrid', {'A': c})))
        return self.a1i(claim, f'{a}p{b}e{a + b}')

    def mp(self, given, claim, hypothesis, implication):
        return self.ap('ax-mp', {'ph': given, 'ps': claim},
                       hypothesis, implication)

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


def terms_of(poly):
    """A polynomial as its terms in canonical order."""
    return [(m, poly.terms[m]) for m in sorted(poly.terms, key=order)]


class Unhandled(Exception):
    """A form this emitter cannot build a proof for.

    The step is refused rather than guessed at, and `elaborate.py` takes it
    as stated instead, which is what it did before this module existed."""
