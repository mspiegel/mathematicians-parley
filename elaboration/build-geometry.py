#!/usr/bin/env python3
"""Generate `geometry.mm`, the facts this corpus needs and set.mm lacks.

The corpus supplies an item in one of two ways: a set.mm label, or a proof
file in the readable layer. Four of the geometry items can take neither.
set.mm has no theorem stating them, and the readable layer cannot state them
either, because saying what they say means dividing one point by another and
naming the branch cut of the complex logarithm. Those are the ℂ encoding,
which `GEOMETRY.md` chose on the understanding that it would reach the reader
as dull facts and not as case splits inside an argument.

So they are proved here, below the readable layer, in the same place
`definitions.mm` puts `df-ang`. A proof file includes this one; the database
names these labels in a `target` the way it names a set.mm label.

Proofs are built rather than written. A Metamath proof is a flat sequence of
labels in reverse Polish, and `ap` assembles one from a label and what it is
applied to, so a statement is written once, in the notation set.mm writes it
in, and never transcribed into stack order by hand.

Usage:  elaboration/build-geometry.py <set.mm>  > elaboration/geometry.mm
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

import kernel
from library import Signature
from library import read as read_library


class Builder:
    """Statements in set.mm's notation, proofs in stack order."""

    def __init__(self, sigs):
        self.sigs = sigs
        self.syntax = kernel.Syntax(sigs)
        self.flabel = {s.statement[1]: label
                       for label, s in sigs.items() if s.kind == '$f'}
        # What a statement asks to be pushed is every variable it mentions,
        # in the order set.mm declares the floats, which is the order they
        # are read in and not the order a statement happens to write them.
        self.forder = {label: i for i, label in enumerate(sigs)}

    def define(self, label, statement):
        """Register a lemma this file proves, so a later one may apply it."""
        tokens = statement.split()
        free = sorted({t for t in tokens if t in self.flabel},
                      key=lambda v: self.forder[self.flabel[v]])
        self.sigs[label] = Signature(
            label, '$p', tokens,
            [(self.sigs[self.flabel[v]].statement[0], v) for v in free])

    def rpn(self, text, start='class'):
        """A term written in set.mm's notation, as the labels that build it."""
        return self.syntax.parse(text.split(), start).rpn(self.flabel)

    def wff(self, text):
        return self.rpn(text, 'wff')

    def ap(self, label, binds=None, *essentials):
        """One step: what the label wants pushed, then what it is applied to.

        The floating hypotheses go first, in the order set.mm declares them,
        each as the term bound to it or as its own variable where the step
        leaves it open; then the proofs of the essential hypotheses, in the
        order the label lists them."""
        sig = self.sigs[label]
        out = [binds[var] if binds and var in binds else self.flabel[var]
               for _typecode, var in sig.floats]
        return ' '.join([*out, *essentials, label])


def triangle(p, q, r):
    """What `def:triangle` says of three points, as set.mm writes it.

    Three distinct points that are not collinear, and in the plane the
    three being collinear is (r − p)/(q − p) being real."""
    return (f'( ( ( -. {p} = {q} /\\ -. {q} = {r} ) /\\ -. {p} = {r} ) '
            f'/\\ -. ( ( {r} - {p} ) / ( {q} - {p} ) ) e. RR )')


def differs(b, under, x, y, mem_x, mem_y, unequal):
    """( under -> ( x - y ) =/= 0 ), given ( under -> -. x = y ).

    A difference is zero exactly when the two are equal, so the point of
    the step is to carry that across the negation."""
    w = {'ph': b.wff(under), 'A': b.rpn(x), 'B': b.rpn(y)}
    return b.ap('mpbird',
                {'ph': b.wff(under), 'ps': b.wff(f'( {x} - {y} ) =/= 0'),
                 'ch': b.wff(f'{x} =/= {y}')},
                b.ap('neqned', w, unequal),
                b.ap('necon3bid',
                     {'ph': b.wff(under), 'A': b.rpn(f'( {x} - {y} )'),
                      'B': b.rpn('0'), 'C': b.rpn(x), 'D': b.rpn(y)},
                     b.ap('subeq0ad', w, mem_x, mem_y)))


def flipped(b, under, x, y, unequal):
    """( under -> -. y = x ), given ( under -> -. x = y )."""
    return b.ap('neneqd', {'ph': b.wff(under), 'A': b.rpn(y), 'B': b.rpn(x)},
                b.ap('necomd',
                     {'ph': b.wff(under), 'A': b.rpn(x), 'B': b.rpn(y)},
                     b.ap('neqned',
                          {'ph': b.wff(under), 'A': b.rpn(x), 'B': b.rpn(y)},
                          unequal)))


def triangle_lemmas(b):
    """Reordering a triangle's vertices, and the fact underneath it.

    A triangle is three distinct points that are not collinear, and in the
    plane the three being collinear is (R − P)/(Q − P) being real. Swapping
    two vertices inverts that quotient and rotating them replaces it by
    (1 − t)/(−t); neither leaves the reals, so neither makes a triangle
    collinear. `gtrirec` is the inversion and the rest is bookkeeping."""
    out = []

    # ( A / B ) is real and nonzero exactly when its inverse is, and its
    # inverse is ( B / A ). Everything below turns on this one step.
    ph = '( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )'
    quo, inv = '( A / B )', '( B / A )'
    psi = f'( {ph} /\\ {quo} e. RR )'

    is_real = b.ap('simpr', {'ph': b.wff(ph), 'ps': b.wff(f'{quo} e. RR')})
    nonzero = b.ap('adantr',
                   {'ph': b.wff(ph), 'ps': b.wff(f'{quo} =/= 0'),
                    'ch': b.wff(f'{quo} e. RR')},
                   b.ap('divne0', {'A': b.rpn('A'), 'B': b.rpn('B')}))
    recip = b.ap('syl',
                 {'ph': b.wff(psi),
                  'ps': b.wff(f'( {quo} e. RR /\\ {quo} =/= 0 )'),
                  'ch': b.wff(f'( 1 / {quo} ) e. RR')},
                 b.ap('jca', {'ph': b.wff(psi),
                              'ps': b.wff(f'{quo} e. RR'),
                              'ch': b.wff(f'{quo} =/= 0')},
                      is_real, nonzero),
                 b.ap('rereccl', {'A': b.rpn(quo)}))
    equals = b.ap('adantr',
                  {'ph': b.wff(ph), 'ps': b.wff(f'( 1 / {quo} ) = {inv}'),
                   'ch': b.wff(f'{quo} e. RR')},
                  b.ap('recdiv', {'A': b.rpn('A'), 'B': b.rpn('B')}))
    under = b.ap('eqeltrrd',
                 {'ph': b.wff(psi), 'A': b.rpn(f'( 1 / {quo} )'),
                  'B': b.rpn(inv), 'C': b.rpn('RR')},
                 equals, recip)
    says = f'|- ( {ph} -> ( {quo} e. RR -> {inv} e. RR ) )'
    out.append((
        'gtrirec', says,
        b.ap('ex', {'ph': b.wff(ph), 'ps': b.wff(f'{quo} e. RR'),
                    'ch': b.wff(f'{inv} e. RR')}, under)))
    b.define('gtrirec', says)

    # Swapping the last two vertices. The three points are the same three,
    # so only the quotient moves, and it moves to its own inverse.
    points = '( A e. CC /\\ B e. CC /\\ C e. CC )'
    given, want = triangle('A', 'B', 'C'), triangle('A', 'C', 'B')
    held = f'( {points} /\\ {given} )'
    w = {'ph': b.wff(points), 'ch': b.wff(given)}

    def member(name, which):
        return b.ap('adantr', {**w, 'ps': b.wff(f'{name} e. CC')},
                    b.ap(which, {'ph': b.wff('A e. CC'),
                                 'ps': b.wff('B e. CC'),
                                 'ch': b.wff('C e. CC')}))

    mem = {'A': member('A', 'simp1'), 'B': member('B', 'simp2'),
           'C': member('C', 'simp3')}
    whole = b.ap('simpr', {'ph': b.wff(points), 'ps': b.wff(given)})
    apart = b.ap('simpld',
                 {'ph': b.wff(held),
                  'ps': b.wff('( ( -. A = B /\\ -. B = C ) /\\ -. A = C )'),
                  'ch': b.wff('-. ( ( C - A ) / ( B - A ) ) e. RR')}, whole)
    straight = b.ap('simprd',
                    {'ph': b.wff(held),
                     'ps': b.wff('( ( -. A = B /\\ -. B = C ) /\\ -. A = C )'),
                     'ch': b.wff('-. ( ( C - A ) / ( B - A ) ) e. RR')}, whole)
    pair = b.ap('simpld',
                {'ph': b.wff(held),
                 'ps': b.wff('( -. A = B /\\ -. B = C )'),
                 'ch': b.wff('-. A = C')}, apart)
    not_ac = b.ap('simprd',
                  {'ph': b.wff(held),
                   'ps': b.wff('( -. A = B /\\ -. B = C )'),
                   'ch': b.wff('-. A = C')}, apart)
    two = {'ph': b.wff(held), 'ps': b.wff('-. A = B'),
           'ch': b.wff('-. B = C')}
    not_ab = b.ap('simpld', two, pair)
    not_bc = b.ap('simprd', two, pair)

    # ( C - A ) and ( B - A ) are the two the quotient is built from, and
    # each is nonzero because A is neither of the other two vertices.
    sides = {}
    for near, far, unequal in (('B', 'A', not_ab), ('C', 'A', not_ac)):
        sides[f'{near}{far}'] = (
            b.ap('subcld', {'ph': b.wff(held), 'A': b.rpn(near),
                            'B': b.rpn(far)}, mem[near], mem[far]),
            differs(b, held, near, far, mem[near], mem[far],
                    flipped(b, held, far, near, unequal)))

    ba, ca = '( B - A )', '( C - A )'
    antecedent = b.ap(
        'jca', {'ph': b.wff(held),
                'ps': b.wff(f'( {ba} e. CC /\\ {ba} =/= 0 )'),
                'ch': b.wff(f'( {ca} e. CC /\\ {ca} =/= 0 )')},
        b.ap('jca', {'ph': b.wff(held), 'ps': b.wff(f'{ba} e. CC'),
                     'ch': b.wff(f'{ba} =/= 0')}, *sides['BA']),
        b.ap('jca', {'ph': b.wff(held), 'ps': b.wff(f'{ca} e. CC'),
                     'ch': b.wff(f'{ca} =/= 0')}, *sides['CA']))
    turned = b.ap(
        'mpd', {'ph': b.wff(held),
                'ps': b.wff(f'-. ( {ca} / {ba} ) e. RR'),
                'ch': b.wff(f'-. ( {ba} / {ca} ) e. RR')},
        straight,
        b.ap('con3d', {'ph': b.wff(held),
                       'ps': b.wff(f'( {ba} / {ca} ) e. RR'),
                       'ch': b.wff(f'( {ca} / {ba} ) e. RR')},
             b.ap('syl',
                  {'ph': b.wff(held),
                   'ps': b.wff(f'( ( {ba} e. CC /\\ {ba} =/= 0 ) '
                               f'/\\ ( {ca} e. CC /\\ {ca} =/= 0 ) )'),
                   'ch': b.wff(f'( ( {ba} / {ca} ) e. RR '
                               f'-> ( {ca} / {ba} ) e. RR )')},
                  antecedent,
                  b.ap('gtrirec', {'A': b.rpn(ba), 'B': b.rpn(ca)}))))

    built = b.ap(
        'jca', {'ph': b.wff(held),
                'ps': b.wff('( ( -. A = C /\\ -. C = B ) /\\ -. A = B )'),
                'ch': b.wff(f'-. ( {ba} / {ca} ) e. RR')},
        b.ap('jca31', {'ph': b.wff(held), 'ps': b.wff('-. A = C'),
                       'ch': b.wff('-. C = B'), 'th': b.wff('-. A = B')},
             not_ac, flipped(b, held, 'B', 'C', not_bc), not_ab),
        turned)
    out.append((
        'gtriswap',
        f'|- ( {points} -> ( {given} -> {want} ) )',
        b.ap('ex', {'ph': b.wff(points), 'ps': b.wff(given),
                    'ch': b.wff(want)}, built)))
    return out


def rotation(b, out):
    """Rotating the vertices, which moves the quotient rather than inverting.

    Swapping two vertices takes (C − A)/(B − A) to its own inverse, but
    rotating them takes it to 1 − (C − B)/(A − B), so the step is an
    identity of the field rather than one fact about reciprocals. The
    identity holds because (A − B) − (C − B) is A − C, and dividing that by
    A − B splits into the two quotients."""
    w3a = '( A e. CC /\\ B e. CC /\\ C e. CC )'
    apart = '( ( A - B ) =/= 0 /\\ ( C - B ) =/= 0 )'
    ph = f'( {w3a} /\\ {apart} )'
    ab, cb, ac = '( A - B )', '( C - B )', '( A - C )'
    quo, inv = f'( {ab} / {cb} )', f'( {cb} / {ab} )'
    goal = '( ( C - A ) / ( B - A ) )'
    psi = f'( {ph} /\\ {quo} e. RR )'

    def under(claim, proof):
        """One proof of ( ph -> claim ), lifted to ( psi -> claim )."""
        return b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(claim),
                               'ch': b.wff(f'{quo} e. RR')}, proof)

    def member(name, which):
        return under(f'{name} e. CC', b.ap(
            'adantr', {'ph': b.wff(w3a), 'ps': b.wff(f'{name} e. CC'),
                       'ch': b.wff(apart)},
            b.ap(which, {'ph': b.wff('A e. CC'), 'ps': b.wff('B e. CC'),
                         'ch': b.wff('C e. CC')})))

    mem = {'A': member('A', 'simp1'), 'B': member('B', 'simp2'),
           'C': member('C', 'simp3')}
    two = {'ph': b.wff(f'{ab} =/= 0'), 'ps': b.wff(f'{cb} =/= 0')}
    nz = {}
    for side, pick in ((ab, 'simpl'), (cb, 'simpr')):
        nz[side] = under(f'{side} =/= 0', b.ap(
            'adantl', {'ph': b.wff(apart), 'ps': b.wff(f'{side} =/= 0'),
                       'ch': b.wff(w3a)},
            b.ap(pick, two)))
    cls = {}
    for side, x, y in ((ab, 'A', 'B'), (cb, 'C', 'B'), (ac, 'A', 'C')):
        cls[side] = b.ap('subcld', {'ph': b.wff(psi), 'A': b.rpn(x),
                                    'B': b.rpn(y)}, mem[x], mem[y])

    # 1 - ( C - B ) / ( A - B ) is real, because the quotient the step is
    # given is, and a quotient is real exactly when its inverse is.
    flipped_real = b.ap(
        'mpd', {'ph': b.wff(psi), 'ps': b.wff(f'{quo} e. RR'),
                'ch': b.wff(f'{inv} e. RR')},
        b.ap('simpr', {'ph': b.wff(ph), 'ps': b.wff(f'{quo} e. RR')}),
        b.ap('syl',
             {'ph': b.wff(psi),
              'ps': b.wff(f'( ( {ab} e. CC /\\ {ab} =/= 0 ) '
                          f'/\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )'),
              'ch': b.wff(f'( {quo} e. RR -> {inv} e. RR )')},
             b.ap('jca',
                  {'ph': b.wff(psi),
                   'ps': b.wff(f'( {ab} e. CC /\\ {ab} =/= 0 )'),
                   'ch': b.wff(f'( {cb} e. CC /\\ {cb} =/= 0 )')},
                  b.ap('jca', {'ph': b.wff(psi), 'ps': b.wff(f'{ab} e. CC'),
                               'ch': b.wff(f'{ab} =/= 0')},
                       cls[ab], nz[ab]),
                  b.ap('jca', {'ph': b.wff(psi), 'ps': b.wff(f'{cb} e. CC'),
                               'ch': b.wff(f'{cb} =/= 0')},
                       cls[cb], nz[cb])),
             b.ap('gtrirec', {'A': b.rpn(ab), 'B': b.rpn(cb)})))
    whole_real = b.ap(
        'syl2anc', {'ph': b.wff(psi), 'ps': b.wff('1 e. RR'),
                    'ch': b.wff(f'{inv} e. RR'),
                    'th': b.wff(f'( 1 - {inv} ) e. RR')},
        b.ap('a1i', {'ph': b.wff('1 e. RR'), 'ps': b.wff(psi)}, '1re'),
        flipped_real,
        b.ap('resubcl', {'A': b.rpn('1'), 'B': b.rpn(inv)}))

    # ( C - A ) / ( B - A ) = 1 - ( C - B ) / ( A - B ), in four moves.
    split = b.ap(
        'syl3anc',
        {'ph': b.wff(psi), 'ps': b.wff(f'{ab} e. CC'),
         'ch': b.wff(f'{cb} e. CC'),
         'th': b.wff(f'( {ab} e. CC /\\ {ab} =/= 0 )'),
         'ta': b.wff(f'( ( {ab} - {cb} ) / {ab} ) '
                     f'= ( ( {ab} / {ab} ) - {inv} )')},
        cls[ab], cls[cb],
        b.ap('jca', {'ph': b.wff(psi), 'ps': b.wff(f'{ab} e. CC'),
                     'ch': b.wff(f'{ab} =/= 0')}, cls[ab], nz[ab]),
        b.ap('divsubdir', {'A': b.rpn(ab), 'B': b.rpn(cb), 'C': b.rpn(ab)}))
    cancels = b.ap(
        'oveq1d', {'ph': b.wff(psi), 'A': b.rpn(f'( {ab} / {ab} )'),
                   'B': b.rpn('1'), 'C': b.rpn(inv), 'F': b.rpn('-')},
        b.ap('syl2anc', {'ph': b.wff(psi), 'ps': b.wff(f'{ab} e. CC'),
                         'ch': b.wff(f'{ab} =/= 0'),
                         'th': b.wff(f'( {ab} / {ab} ) = 1')},
             cls[ab], nz[ab], b.ap('divid', {'A': b.rpn(ab)})))
    joins = b.ap(
        'oveq1d', {'ph': b.wff(psi), 'A': b.rpn(f'( {ab} - {cb} )'),
                   'B': b.rpn(ac), 'C': b.rpn(ab), 'F': b.rpn('/')},
        b.ap('syl3anc', {'ph': b.wff(psi), 'ps': b.wff('A e. CC'),
                         'ch': b.wff('C e. CC'), 'th': b.wff('B e. CC'),
                         'ta': b.wff(f'( {ab} - {cb} ) = {ac}')},
             mem['A'], mem['C'], mem['B'],
             b.ap('nnncan2', {'A': b.rpn('A'), 'B': b.rpn('C'),
                              'C': b.rpn('B')})))
    negated = b.ap(
        'syl3anc', {'ph': b.wff(psi), 'ps': b.wff(f'{ac} e. CC'),
                    'ch': b.wff(f'{ab} e. CC'), 'th': b.wff(f'{ab} =/= 0'),
                    'ta': b.wff(f'( -u {ac} / -u {ab} ) = ( {ac} / {ab} )')},
        cls[ac], cls[ab], nz[ab],
        b.ap('div2neg', {'A': b.rpn(ac), 'B': b.rpn(ab)}))
    turned = b.ap(
        'oveq12d', {'ph': b.wff(psi), 'A': b.rpn(f'-u {ac}'),
                    'B': b.rpn('( C - A )'), 'C': b.rpn(f'-u {ab}'),
                    'D': b.rpn('( B - A )'), 'F': b.rpn('/')},
        b.ap('syl2anc', {'ph': b.wff(psi), 'ps': b.wff('A e. CC'),
                         'ch': b.wff('C e. CC'),
                         'th': b.wff(f'-u {ac} = ( C - A )')},
             mem['A'], mem['C'],
             b.ap('negsubdi2', {'A': b.rpn('A'), 'B': b.rpn('C')})),
        b.ap('syl2anc', {'ph': b.wff(psi), 'ps': b.wff('A e. CC'),
                         'ch': b.wff('B e. CC'),
                         'th': b.wff(f'-u {ab} = ( B - A )')},
             mem['A'], mem['B'],
             b.ap('negsubdi2', {'A': b.rpn('A'), 'B': b.rpn('B')})))
    same = b.ap(
        '3eqtr3d', {'ph': b.wff(psi), 'A': b.rpn(f'( -u {ac} / -u {ab} )'),
                    'B': b.rpn(f'( {ac} / {ab} )'), 'C': b.rpn(goal),
                    'D': b.rpn(f'( 1 - {inv} )')},
        negated, turned,
        b.ap('eqtr3d', {'ph': b.wff(psi),
                        'A': b.rpn(f'( ( {ab} - {cb} ) / {ab} )'),
                        'B': b.rpn(f'( {ac} / {ab} )'),
                        'C': b.rpn(f'( 1 - {inv} )')},
             joins, b.ap('eqtrd',
                         {'ph': b.wff(psi),
                          'A': b.rpn(f'( ( {ab} - {cb} ) / {ab} )'),
                          'B': b.rpn(f'( ( {ab} / {ab} ) - {inv} )'),
                          'C': b.rpn(f'( 1 - {inv} )')}, split, cancels)))
    reached = b.ap('eqeltrd', {'ph': b.wff(psi), 'A': b.rpn(goal),
                               'B': b.rpn(f'( 1 - {inv} )'),
                               'C': b.rpn('RR')}, same, whole_real)
    says = f'|- ( {ph} -> ( {quo} e. RR -> {goal} e. RR ) )'
    out.append(('gtricol', says,
                b.ap('ex', {'ph': b.wff(ph), 'ps': b.wff(f'{quo} e. RR'),
                            'ch': b.wff(f'{goal} e. RR')}, reached)))
    b.define('gtricol', says)

    # Rotating all three vertices, which the isosceles proof cites once.
    points = '( A e. CC /\\ B e. CC /\\ C e. CC )'
    given, want = triangle('A', 'B', 'C'), triangle('B', 'C', 'A')
    held = f'( {points} /\\ {given} )'

    def member(name, which):
        return b.ap('adantr', {'ph': b.wff(points),
                               'ps': b.wff(f'{name} e. CC'),
                               'ch': b.wff(given)},
                    b.ap(which, {'ph': b.wff('A e. CC'),
                                 'ps': b.wff('B e. CC'),
                                 'ch': b.wff('C e. CC')}))

    mem = {'A': member('A', 'simp1'), 'B': member('B', 'simp2'),
           'C': member('C', 'simp3')}
    inner = '( ( -. A = B /\\ -. B = C ) /\\ -. A = C )'
    straightness = '-. ( ( C - A ) / ( B - A ) ) e. RR'
    whole = b.ap('simpr', {'ph': b.wff(points), 'ps': b.wff(given)})
    apart_of = {'ph': b.wff(held), 'ps': b.wff(inner),
                'ch': b.wff(straightness)}
    distinct = b.ap('simpld', apart_of, whole)
    straight = b.ap('simprd', apart_of, whole)
    pair_of = {'ph': b.wff(held), 'ps': b.wff('( -. A = B /\\ -. B = C )'),
               'ch': b.wff('-. A = C')}
    pair = b.ap('simpld', pair_of, distinct)
    not_ac = b.ap('simprd', pair_of, distinct)
    two_of = {'ph': b.wff(held), 'ps': b.wff('-. A = B'),
              'ch': b.wff('-. B = C')}
    not_ab = b.ap('simpld', two_of, pair)
    not_bc = b.ap('simprd', two_of, pair)

    turned = b.ap(
        'mpd', {'ph': b.wff(held), 'ps': b.wff(straightness),
                'ch': b.wff(f'-. {quo} e. RR')},
        straight,
        b.ap('con3d', {'ph': b.wff(held), 'ps': b.wff(f'{quo} e. RR'),
                       'ch': b.wff(f'{goal} e. RR')},
             b.ap('syl', {'ph': b.wff(held), 'ps': b.wff(ph),
                          'ch': b.wff(f'( {quo} e. RR -> {goal} e. RR )')},
                  b.ap('jca', {'ph': b.wff(held), 'ps': b.wff(points),
                               'ch': b.wff(apart)},
                       b.ap('simpl', {'ph': b.wff(points),
                                      'ps': b.wff(given)}),
                       b.ap('jca', {'ph': b.wff(held),
                                    'ps': b.wff(f'{ab} =/= 0'),
                                    'ch': b.wff(f'{cb} =/= 0')},
                            differs(b, held, 'A', 'B', mem['A'], mem['B'],
                                    not_ab),
                            differs(b, held, 'C', 'B', mem['C'], mem['B'],
                                    flipped(b, held, 'B', 'C', not_bc)))),
                  b.ap('gtricol'))))
    built = b.ap(
        'jca', {'ph': b.wff(held),
                'ps': b.wff('( ( -. B = C /\\ -. C = A ) /\\ -. B = A )'),
                'ch': b.wff(f'-. {quo} e. RR')},
        b.ap('jca31', {'ph': b.wff(held), 'ps': b.wff('-. B = C'),
                       'ch': b.wff('-. C = A'), 'th': b.wff('-. B = A')},
             not_bc, flipped(b, held, 'A', 'C', not_ac),
             flipped(b, held, 'A', 'B', not_ab)),
        turned)
    out.append((
        'gtrirotate',
        f'|- ( {points} -> ( {given} -> {want} ) )',
        b.ap('ex', {'ph': b.wff(points), 'ps': b.wff(given),
                    'ch': b.wff(want)}, built)))
    return out


HEAD = """$( geometry, built by elaboration/build-geometry.py.

   What this corpus needs of the plane and set.mm does not state.
   Points are complex numbers, distance is the absolute value of a
   difference, and the angle is the constant definitions.mm introduces,
   so everything here is a theorem rather than an axiom: CC is a model
   and nothing in it has to be assumed.  GEOMETRY.md takes that
   decision and says what it costs. $)

$[ definitions.mm $]

"""


def main(argv):
    if len(argv) < 2:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    sigs = read_library(argv[1])
    b = Builder(sigs)
    print(HEAD, end='')
    for label, statement, proof in rotation(b, triangle_lemmas(b)):
        print(f'  {label} $p {statement} $=')
        line = '   '
        for token in proof.split():
            if len(line) + len(token) > 76:
                print(line)
                line = '   '
            line += ' ' + token
        print(f'{line} $.')
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
