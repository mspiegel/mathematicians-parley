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


def terms_of(poly):
    """A polynomial as its terms in canonical order."""
    return [(m, poly.terms[m]) for m in sorted(poly.terms, key=order)]
