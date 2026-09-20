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


def angle_symmetry(b, out):
    """The angle from A to B and the angle from B to A have one size.

    `ang` is signed and lands in −pi to pi, so the two are not equal; the
    corpus writes the unsigned angle, which is this one's absolute value,
    and those do agree. Off the branch cut that is `arginv`, which says the
    signed angle of an inverse is the negative of the angle. On the cut
    `arginv` does not apply and nothing is negated: `lognegb` says a number
    whose negative is a positive real has angle pi exactly, and the inverse
    of such a number is another, so both angles are pi."""
    ph = '( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )'
    z, rz = '( B / A )', '( 1 / ( B / A ) )'
    theta, rtheta = f'( Im ` ( log ` {z} ) )', f'( Im ` ( log ` {rz} ) )'
    cut = f'-u {z} e. RR+'

    left = b.ap('simpl', {'ph': b.wff('( A e. CC /\\ A =/= 0 )'),
                          'ps': b.wff('( B e. CC /\\ B =/= 0 )')})
    right = b.ap('simpr', {'ph': b.wff('( A e. CC /\\ A =/= 0 )'),
                           'ps': b.wff('( B e. CC /\\ B =/= 0 )')})
    part = {}
    for name, whole, which in (('Acc', left, 'simpld'), ('Anz', left, 'simprd'),
                               ('Bcc', right, 'simpld'),
                               ('Bnz', right, 'simprd')):
        one = 'A' if whole is left else 'B'
        part[name] = b.ap(which, {'ph': b.wff(ph),
                                  'ps': b.wff(f'{one} e. CC'),
                                  'ch': b.wff(f'{one} =/= 0')}, whole)
    z_cc = b.ap('syl3anc', {'ph': b.wff(ph), 'ps': b.wff('B e. CC'),
                            'ch': b.wff('A e. CC'), 'th': b.wff('A =/= 0'),
                            'ta': b.wff(f'{z} e. CC')},
                part['Bcc'], part['Acc'], part['Anz'],
                b.ap('divcl', {'A': b.rpn('B'), 'B': b.rpn('A')}))
    z_nz = b.ap('syl', {'ph': b.wff(ph),
                        'ps': b.wff('( ( B e. CC /\\ B =/= 0 ) '
                                    '/\\ ( A e. CC /\\ A =/= 0 ) )'),
                        'ch': b.wff(f'{z} =/= 0')},
                b.ap('jca', {'ph': b.wff(ph),
                             'ps': b.wff('( B e. CC /\\ B =/= 0 )'),
                             'ch': b.wff('( A e. CC /\\ A =/= 0 )')},
                     right, left),
                b.ap('divne0', {'A': b.rpn('B'), 'B': b.rpn('A')}))

    # ( A ang B ) is the angle of B / A, and ( B ang A ) that of its inverse.
    value = b.ap('angval', {'A': b.rpn('A'), 'B': b.rpn('B'),
                            'F': b.rpn('ang')}, b.ap('df-ang'))
    other = '( Im ` ( log ` ( A / B ) ) )'
    flipped_ph = ('( ( B e. CC /\\ B =/= 0 ) /\\ ( A e. CC /\\ A =/= 0 ) )')
    other_way = b.ap('jca', {'ph': b.wff(ph),
                             'ps': b.wff('( B e. CC /\\ B =/= 0 )'),
                             'ch': b.wff('( A e. CC /\\ A =/= 0 )')},
                     right, left)
    # A / B is the inverse of B / A, so the second angle is the angle of
    # the inverse and the two lemmas below are about one number.
    inverts = b.ap('eqcomd', {'ph': b.wff(ph), 'A': b.rpn(rz),
                              'B': b.rpn('( A / B )')},
                   b.ap('syl', {'ph': b.wff(ph), 'ps': b.wff(flipped_ph),
                                'ch': b.wff(f'{rz} = ( A / B )')},
                        other_way,
                        b.ap('recdiv', {'A': b.rpn('B'), 'B': b.rpn('A')})))
    reads = b.ap('fveq2d', {'ph': b.wff(ph),
                            'A': b.rpn('( log ` ( A / B ) )'),
                            'B': b.rpn(f'( log ` {rz} )'), 'F': b.rpn('Im')},
                 b.ap('fveq2d', {'ph': b.wff(ph), 'A': b.rpn('( A / B )'),
                                 'B': b.rpn(rz), 'F': b.rpn('log')},
                      inverts))
    swapped = b.ap('eqtrd', {'ph': b.wff(ph), 'A': b.rpn('( B ang A )'),
                             'B': b.rpn(other), 'C': b.rpn(rtheta)},
                   b.ap('ancoms', {'ph': b.wff('( B e. CC /\\ B =/= 0 )'),
                                   'ps': b.wff('( A e. CC /\\ A =/= 0 )'),
                                   'ch': b.wff(f'( B ang A ) = {other}')},
                        b.ap('angval', {'A': b.rpn('B'), 'B': b.rpn('A'),
                                        'F': b.rpn('ang')}, b.ap('df-ang'))),
                   reads)
    for label, says, proof in (
            ('gangval', f'|- ( {ph} -> ( A ang B ) = {theta} )', value),
            ('gangrec', f'|- ( {ph} -> ( B ang A ) = {rtheta} )', swapped)):
        out.append((label, says, proof))
        b.define(label, says)

    # Off the branch cut the two angles are negatives of one another, and
    # an absolute value does not tell them apart.
    off = f'( {ph} /\\ -. {cut} )'
    free = b.ap(
        'fveq2d', {'ph': b.wff(off), 'A': b.rpn(rtheta),
                   'B': b.rpn(f'-u {theta}'), 'F': b.rpn('abs')},
        b.ap('arginv', {'ph': b.wff(off), 'A': b.rpn(z)},
             b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} e. CC'),
                             'ch': b.wff(f'-. {cut}')}, z_cc),
             b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} =/= 0'),
                             'ch': b.wff(f'-. {cut}')}, z_nz),
             b.ap('simpr', {'ph': b.wff(ph), 'ps': b.wff(f'-. {cut}')})))
    angle_cc = b.ap(
        'syl', {'ph': b.wff(off), 'ps': b.wff(f'{theta} e. RR'),
                'ch': b.wff(f'{theta} e. CC')},
        b.ap('syl', {'ph': b.wff(off), 'ps': b.wff(f'( log ` {z} ) e. CC'),
                     'ch': b.wff(f'{theta} e. RR')},
             b.ap('logcld', {'ph': b.wff(off), 'X': b.rpn(z)},
                  b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} e. CC'),
                                  'ch': b.wff(f'-. {cut}')}, z_cc),
                  b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} =/= 0'),
                                  'ch': b.wff(f'-. {cut}')}, z_nz)),
             b.ap('imcl', {'A': b.rpn(f'( log ` {z} )')})),
        b.ap('recn', {'A': b.rpn(theta)}))
    outside = b.ap(
        'eqcomd', {'ph': b.wff(off), 'A': b.rpn(f'( abs ` {rtheta} )'),
                   'B': b.rpn(f'( abs ` {theta} )')},
        b.ap('eqtrd', {'ph': b.wff(off), 'A': b.rpn(f'( abs ` {rtheta} )'),
                       'B': b.rpn(f'( abs ` -u {theta} )'),
                       'C': b.rpn(f'( abs ` {theta} )')},
             free,
             b.ap('syl', {'ph': b.wff(off), 'ps': b.wff(f'{theta} e. CC'),
                          'ch': b.wff(f'( abs ` -u {theta} ) '
                                      f'= ( abs ` {theta} )')},
                  angle_cc, b.ap('absneg', {'A': b.rpn(theta)}))))

    # On the cut neither angle is negated: both are pi exactly.
    on = f'( {ph} /\\ {cut} )'

    def is_pi(what, whole, nonzero, positive):
        return b.ap('mpbid', {'ph': b.wff(on), 'ps': b.wff(f'-u {what} e. RR+'),
                              'ch': b.wff(f'( Im ` ( log ` {what} ) ) = _pi')},
                    positive,
                    b.ap('syl2anc', {'ph': b.wff(on),
                                     'ps': b.wff(f'{what} e. CC'),
                                     'ch': b.wff(f'{what} =/= 0'),
                                     'th': b.wff(f'( -u {what} e. RR+ <-> '
                                                 f'( Im ` ( log ` {what} ) ) '
                                                 f'= _pi )')},
                         whole, nonzero,
                         b.ap('lognegb', {'A': b.rpn(what)})))

    z_cc_on = b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} e. CC'),
                              'ch': b.wff(cut)}, z_cc)
    z_nz_on = b.ap('adantr', {'ph': b.wff(ph), 'ps': b.wff(f'{z} =/= 0'),
                              'ch': b.wff(cut)}, z_nz)
    held = b.ap('simpr', {'ph': b.wff(ph), 'ps': b.wff(cut)})
    # -u ( 1 / z ) is ( 1 / -u z ), and the reciprocal of a positive real
    # is one, so the inverse sits on the cut whenever z does.
    rz_positive = b.ap(
        'eqeltrrd', {'ph': b.wff(on), 'A': b.rpn(f'( 1 / -u {z} )'),
                     'B': b.rpn(f'-u {rz}'), 'C': b.rpn('RR+')},
        b.ap('eqcomd', {'ph': b.wff(on), 'A': b.rpn(f'-u {rz}'),
                        'B': b.rpn(f'( 1 / -u {z} )')},
             b.ap('syl3anc',
                  {'ph': b.wff(on), 'ps': b.wff('1 e. CC'),
                   'ch': b.wff(f'{z} e. CC'), 'th': b.wff(f'{z} =/= 0'),
                   'ta': b.wff(f'-u {rz} = ( 1 / -u {z} )')},
                  b.ap('a1i', {'ph': b.wff('1 e. CC'), 'ps': b.wff(on)},
                       'ax-1cn'),
                  z_cc_on, z_nz_on,
                  b.ap('divneg2', {'A': b.rpn('1'), 'B': b.rpn(z)}))),
        b.ap('syl', {'ph': b.wff(on), 'ps': b.wff(f'-u {z} e. RR+'),
                     'ch': b.wff(f'( 1 / -u {z} ) e. RR+')},
             held, b.ap('rpreccl', {'A': b.rpn(f'-u {z}')})))
    inside = b.ap(
        'eqtr4d', {'ph': b.wff(on), 'A': b.rpn(f'( abs ` {theta} )'),
                   'B': b.rpn('( abs ` _pi )'),
                   'C': b.rpn(f'( abs ` {rtheta} )')},
        b.ap('fveq2d', {'ph': b.wff(on), 'A': b.rpn(theta),
                        'B': b.rpn('_pi'), 'F': b.rpn('abs')},
             is_pi(z, z_cc_on, z_nz_on, held)),
        b.ap('fveq2d', {'ph': b.wff(on), 'A': b.rpn(rtheta),
                        'B': b.rpn('_pi'), 'F': b.rpn('abs')},
             is_pi(rz,
                   b.ap('reccld', {'ph': b.wff(on), 'A': b.rpn(z)},
                        z_cc_on, z_nz_on),
                   b.ap('recne0d', {'ph': b.wff(on), 'A': b.rpn(z)},
                        z_cc_on, z_nz_on),
                   rz_positive)))

    says = (f'|- ( {ph} -> ( abs ` ( A ang B ) ) '
            f'= ( abs ` ( B ang A ) ) ) ')
    joined = b.ap(
        'pm2.61dan', {'ph': b.wff(ph), 'ps': b.wff(cut),
                      'ch': b.wff(f'( abs ` {theta} ) = ( abs ` {rtheta} )')},
        inside, outside)
    whole = b.ap(
        '3eqtr4d', {'ph': b.wff(ph), 'A': b.rpn(f'( abs ` {theta} )'),
                    'B': b.rpn(f'( abs ` {rtheta} )'),
                    'C': b.rpn('( abs ` ( A ang B ) )'),
                    'D': b.rpn('( abs ` ( B ang A ) )')},
        joined,
        b.ap('fveq2d', {'ph': b.wff(ph), 'A': b.rpn('( A ang B )'),
                        'B': b.rpn(theta), 'F': b.rpn('abs')}, value),
        b.ap('fveq2d', {'ph': b.wff(ph), 'A': b.rpn('( B ang A )'),
                        'B': b.rpn(rtheta), 'F': b.rpn('abs')}, swapped))
    out.append(('gangsym', says.strip(), whole))
    b.define('gangsym', says.strip())

    # The same on three points, which is how the corpus states it: the
    # angle at B is between the two differences, and each is nonzero
    # because B is neither of the other two.
    points = '( A e. CC /\\ B e. CC /\\ C e. CC )'
    apart = '( -. A = B /\\ -. C = B )'
    held = f'( {points} /\\ {apart} )'
    ab, cb = '( A - B )', '( C - B )'
    claim = (f'( abs ` ( {ab} ang {cb} ) ) '
             f'= ( abs ` ( {cb} ang {ab} ) )')

    def member(name, which):
        return b.ap('adantr', {'ph': b.wff(points),
                               'ps': b.wff(f'{name} e. CC'),
                               'ch': b.wff(apart)},
                    b.ap(which, {'ph': b.wff('A e. CC'),
                                 'ps': b.wff('B e. CC'),
                                 'ch': b.wff('C e. CC')}))

    mem = {'A': member('A', 'simp1'), 'B': member('B', 'simp2'),
           'C': member('C', 'simp3')}
    two = {'ph': b.wff('-. A = B'), 'ps': b.wff('-. C = B')}
    unequal = {}
    for name, pick in (('AB', 'simpl'), ('CB', 'simpr')):
        unequal[name] = b.ap(
            'adantl', {'ph': b.wff(apart),
                       'ps': b.wff('-. A = B' if name == 'AB'
                                   else '-. C = B'),
                       'ch': b.wff(points)},
            b.ap(pick, two))
    ready = b.ap(
        'jca', {'ph': b.wff(held),
                'ps': b.wff(f'( {ab} e. CC /\\ {ab} =/= 0 )'),
                'ch': b.wff(f'( {cb} e. CC /\\ {cb} =/= 0 )')},
        b.ap('jca', {'ph': b.wff(held), 'ps': b.wff(f'{ab} e. CC'),
                     'ch': b.wff(f'{ab} =/= 0')},
             b.ap('subcld', {'ph': b.wff(held), 'A': b.rpn('A'),
                             'B': b.rpn('B')}, mem['A'], mem['B']),
             differs(b, held, 'A', 'B', mem['A'], mem['B'], unequal['AB'])),
        b.ap('jca', {'ph': b.wff(held), 'ps': b.wff(f'{cb} e. CC'),
                     'ch': b.wff(f'{cb} =/= 0')},
             b.ap('subcld', {'ph': b.wff(held), 'A': b.rpn('C'),
                             'B': b.rpn('B')}, mem['C'], mem['B']),
             differs(b, held, 'C', 'B', mem['C'], mem['B'], unequal['CB'])))
    out.append((
        'gangsym3',
        f'|- ( {points} -> ( {apart} -> {claim} ) )',
        b.ap('ex', {'ph': b.wff(points), 'ps': b.wff(apart),
                    'ch': b.wff(claim)},
             b.ap('syl',
                  {'ph': b.wff(held),
                   'ps': b.wff(f'( ( {ab} e. CC /\\ {ab} =/= 0 ) '
                               f'/\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )'),
                   'ch': b.wff(claim)},
                  ready,
                  b.ap('gangsym', {'A': b.rpn(ab), 'B': b.rpn(cb)})))))
    return out


def angle_size(b, out):
    """Where the unsigned angle lives, and what cosine makes of it.

    Two facts the law of cosines needs. `lawcos` states itself with the
    signed angle, and the corpus writes the unsigned one, so a step that
    carries an angle between the two has to know that cosine cannot tell
    them apart, and that going back is possible because cosine is one to
    one on the range the unsigned angle occupies."""
    # Cosine is even, so it reads an absolute value and the sign it lost.
    real = 'A e. RR'
    same = '( cos ` ( abs ` A ) ) = ( cos ` A )'
    says = f'|- ( {real} -> {same} )'
    out.append(('gcosabs', says, b.ap(
        'lecasei', {'ph': b.wff(real), 'ps': b.wff(same), 'A': b.rpn('0'),
                    'B': b.rpn('A')},
        b.ap('a1i', {'ph': b.wff('0 e. RR'), 'ps': b.wff(real)}, '0re'),
        b.ap('id', {'ph': b.wff(real)}),
        b.ap('fveq2d', {'ph': b.wff(f'( {real} /\\ 0 <_ A )'),
                        'A': b.rpn('( abs ` A )'), 'B': b.rpn('A'),
                        'F': b.rpn('cos')},
             b.ap('absid', {'A': b.rpn('A')})),
        b.ap('eqtrd', {'ph': b.wff(f'( {real} /\\ A <_ 0 )'),
                       'A': b.rpn('( cos ` ( abs ` A ) )'),
                       'B': b.rpn('( cos ` -u A )'),
                       'C': b.rpn('( cos ` A )')},
             b.ap('fveq2d', {'ph': b.wff(f'( {real} /\\ A <_ 0 )'),
                             'A': b.rpn('( abs ` A )'), 'B': b.rpn('-u A'),
                             'F': b.rpn('cos')},
                  b.ap('absnid', {'A': b.rpn('A')})),
             b.ap('syl', {'ph': b.wff(f'( {real} /\\ A <_ 0 )'),
                          'ps': b.wff('A e. CC'),
                          'ch': b.wff('( cos ` -u A ) = ( cos ` A )')},
                  b.ap('recnd', {'ph': b.wff(f'( {real} /\\ A <_ 0 )'),
                                 'A': b.rpn('A')},
                       b.ap('simpl', {'ph': b.wff(real),
                                      'ps': b.wff('A <_ 0')})),
                  b.ap('cosneg', {'A': b.rpn('A')}))))))
    b.define('gcosabs', says)

    # The signed angle sits in -pi to pi, half-open at the bottom, so the
    # unsigned one sits in 0 to pi and `cos11` applies to it.
    ph = '( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )'
    z = '( B / A )'
    theta = f'( Im ` ( log ` {z} ) )'
    size = '( abs ` ( A ang B ) )'
    left = b.ap('simpl', {'ph': b.wff('( A e. CC /\\ A =/= 0 )'),
                          'ps': b.wff('( B e. CC /\\ B =/= 0 )')})
    right = b.ap('simpr', {'ph': b.wff('( A e. CC /\\ A =/= 0 )'),
                           'ps': b.wff('( B e. CC /\\ B =/= 0 )')})
    z_cc = b.ap('syl3anc', {'ph': b.wff(ph), 'ps': b.wff('B e. CC'),
                            'ch': b.wff('A e. CC'), 'th': b.wff('A =/= 0'),
                            'ta': b.wff(f'{z} e. CC')},
                b.ap('simpld', {'ph': b.wff(ph), 'ps': b.wff('B e. CC'),
                                'ch': b.wff('B =/= 0')}, right),
                b.ap('simpld', {'ph': b.wff(ph), 'ps': b.wff('A e. CC'),
                                'ch': b.wff('A =/= 0')}, left),
                b.ap('simprd', {'ph': b.wff(ph), 'ps': b.wff('A e. CC'),
                                'ch': b.wff('A =/= 0')}, left),
                b.ap('divcl', {'A': b.rpn('B'), 'B': b.rpn('A')}))
    z_nz = b.ap('syl', {'ph': b.wff(ph),
                        'ps': b.wff('( ( B e. CC /\\ B =/= 0 ) '
                                    '/\\ ( A e. CC /\\ A =/= 0 ) )'),
                        'ch': b.wff(f'{z} =/= 0')},
                b.ap('jca', {'ph': b.wff(ph),
                             'ps': b.wff('( B e. CC /\\ B =/= 0 )'),
                             'ch': b.wff('( A e. CC /\\ A =/= 0 )')},
                     right, left),
                b.ap('divne0', {'A': b.rpn('B'), 'B': b.rpn('A')}))
    bounds = b.ap('syl2anc', {'ph': b.wff(ph), 'ps': b.wff(f'{z} e. CC'),
                              'ch': b.wff(f'{z} =/= 0'),
                              'th': b.wff(f'( -u _pi < {theta} '
                                          f'/\\ {theta} <_ _pi )')},
                  z_cc, z_nz, b.ap('logimcl', {'A': b.rpn(z)}))
    theta_re = b.ap('imcld', {'ph': b.wff(ph), 'A': b.rpn(f'( log ` {z} )')},
                    b.ap('logcld', {'ph': b.wff(ph), 'X': b.rpn(z)},
                         z_cc, z_nz))
    # -pi < theta gives -pi <_ theta, which is the half `absle` wants.
    under = b.ap('mpbir2and',
                 {'ph': b.wff(ph), 'ps': b.wff(f'( abs ` {theta} ) <_ _pi'),
                  'ch': b.wff(f'-u _pi <_ {theta}'),
                  'th': b.wff(f'{theta} <_ _pi')},
                 b.ap('ltled', {'ph': b.wff(ph), 'A': b.rpn('-u _pi'),
                                'B': b.rpn(theta)},
                      b.ap('a1i', {'ph': b.wff('-u _pi e. RR'),
                                   'ps': b.wff(ph)},
                           b.ap('ax-mp', {'ph': b.wff('_pi e. RR'),
                                          'ps': b.wff('-u _pi e. RR')},
                                'pire',
                                b.ap('renegcl', {'A': b.rpn('_pi')}))),
                      theta_re,
                      b.ap('simpld', {'ph': b.wff(ph),
                                      'ps': b.wff(f'-u _pi < {theta}'),
                                      'ch': b.wff(f'{theta} <_ _pi')},
                           bounds)),
                 b.ap('simprd', {'ph': b.wff(ph),
                                 'ps': b.wff(f'-u _pi < {theta}'),
                                 'ch': b.wff(f'{theta} <_ _pi')}, bounds),
                 b.ap('syl2anc', {'ph': b.wff(ph), 'ps': b.wff(f'{theta} e. RR'),
                                  'ch': b.wff('_pi e. RR'),
                                  'th': b.wff(f'( ( abs ` {theta} ) <_ _pi '
                                              f'<-> ( -u _pi <_ {theta} '
                                              f'/\\ {theta} <_ _pi ) )')},
                      theta_re,
                      b.ap('a1i', {'ph': b.wff('_pi e. RR'),
                                   'ps': b.wff(ph)}, 'pire'),
                      b.ap('absle', {'A': b.rpn(theta), 'B': b.rpn('_pi')})))
    lands = b.ap(
        'mpbir3and',
        {'ph': b.wff(ph), 'ps': b.wff(f'( abs ` {theta} ) e. ( 0 [,] _pi )'),
         'ch': b.wff(f'( abs ` {theta} ) e. RR'),
         'th': b.wff(f'0 <_ ( abs ` {theta} )'),
         'ta': b.wff(f'( abs ` {theta} ) <_ _pi')},
        b.ap('syl', {'ph': b.wff(ph), 'ps': b.wff(f'{theta} e. CC'),
                     'ch': b.wff(f'( abs ` {theta} ) e. RR')},
             b.ap('recnd', {'ph': b.wff(ph), 'A': b.rpn(theta)}, theta_re),
             b.ap('abscl', {'A': b.rpn(theta)})),
        b.ap('syl', {'ph': b.wff(ph), 'ps': b.wff(f'{theta} e. CC'),
                     'ch': b.wff(f'0 <_ ( abs ` {theta} )')},
             b.ap('recnd', {'ph': b.wff(ph), 'A': b.rpn(theta)}, theta_re),
             b.ap('absge0', {'A': b.rpn(theta)})),
        under,
        b.ap('syl2anc', {'ph': b.wff(ph), 'ps': b.wff('0 e. RR'),
                         'ch': b.wff('_pi e. RR'),
                         'th': b.wff(f'( ( abs ` {theta} ) e. ( 0 [,] _pi ) '
                                     f'<-> ( ( abs ` {theta} ) e. RR '
                                     f'/\\ 0 <_ ( abs ` {theta} ) '
                                     f'/\\ ( abs ` {theta} ) <_ _pi ) )')},
             b.ap('a1i', {'ph': b.wff('0 e. RR'), 'ps': b.wff(ph)}, '0re'),
             b.ap('a1i', {'ph': b.wff('_pi e. RR'), 'ps': b.wff(ph)}, 'pire'),
             b.ap('elicc2', {'A': b.rpn('0'), 'B': b.rpn('_pi'),
                             'C': b.rpn(f'( abs ` {theta} )')})))
    says = f'|- ( {ph} -> {size} e. ( 0 [,] _pi ) )'
    out.append(('gangrange', says, b.ap(
        'eqeltrd', {'ph': b.wff(ph), 'A': b.rpn(size),
                    'B': b.rpn(f'( abs ` {theta} )'),
                    'C': b.rpn('( 0 [,] _pi )')},
        b.ap('fveq2d', {'ph': b.wff(ph), 'A': b.rpn('( A ang B )'),
                        'B': b.rpn(theta), 'F': b.rpn('abs')},
             b.ap('gangval', {'A': b.rpn('A'), 'B': b.rpn('B')})),
        lands)))
    b.define('gangrange', says)
    return out


def law_of_cosines(b, out):
    """set.mm's law of cosines, said the way this corpus says things.

    `lawcos` takes the angle function as a hypothesis, and the function it
    takes is `df-ang` to the token, which is why the corpus declares that
    constant and not another. Two things still have to move: `lawcos` names
    the third side |C − B| where the corpus names it |B − C|, and it uses
    the signed angle where the corpus uses the unsigned one. `abssub` and
    `gcosabs` are those two steps."""
    points = '( A e. CC /\\ B e. CC /\\ C e. CC )'
    apart = '( -. A = B /\\ -. C = B )'
    ph = f'( {points} /\\ {apart} )'
    ab, cb, bc, ca = '( A - B )', '( C - B )', '( B - C )', '( C - A )'
    signed = f'( {ab} ang {cb} )'

    def member(name, which):
        return b.ap('adantr', {'ph': b.wff(points),
                               'ps': b.wff(f'{name} e. CC'),
                               'ch': b.wff(apart)},
                    b.ap(which, {'ph': b.wff('A e. CC'),
                                 'ps': b.wff('B e. CC'),
                                 'ch': b.wff('C e. CC')}))

    mem = {'A': member('A', 'simp1'), 'B': member('B', 'simp2'),
           'C': member('C', 'simp3')}
    two = {'ph': b.wff('-. A = B'), 'ps': b.wff('-. C = B')}
    unequal = {}
    for name, pick, claim in (('AB', 'simpl', '-. A = B'),
                              ('CB', 'simpr', '-. C = B')):
        unequal[name] = b.ap('adantl', {'ph': b.wff(apart),
                                        'ps': b.wff(claim),
                                        'ch': b.wff(points)},
                             b.ap(pick, two))

    # lawcos asks for the two disequalities the other way round, and as
    # =/= rather than as a negated equation.
    def ne(x, y, which):
        return b.ap('neqned', {'ph': b.wff(ph), 'A': b.rpn(x),
                               'B': b.rpn(y)}, unequal[which])

    raw = b.ap('syl2anc',
               {'ph': b.wff(ph),
                'ps': b.wff('( C e. CC /\\ A e. CC /\\ B e. CC )'),
                'ch': b.wff('( C =/= B /\\ A =/= B )'),
                'th': b.wff(f'( ( abs ` {ca} ) ^ 2 ) = ( ( ( ( abs ` {ab} ) '
                            f'^ 2 ) + ( ( abs ` {cb} ) ^ 2 ) ) - ( 2 x. ( ( '
                            f'( abs ` {ab} ) x. ( abs ` {cb} ) ) x. '
                            f'( cos ` {signed} ) ) ) )')},
               b.ap('3jca', {'ph': b.wff(ph), 'ps': b.wff('C e. CC'),
                             'ch': b.wff('A e. CC'), 'th': b.wff('B e. CC')},
                    mem['C'], mem['A'], mem['B']),
               b.ap('jca', {'ph': b.wff(ph), 'ps': b.wff('C =/= B'),
                            'ch': b.wff('A =/= B')},
                    ne('C', 'B', 'CB'), ne('A', 'B', 'AB')),
               b.ap('lawcos',
                    {'A': b.rpn('C'), 'B': b.rpn('A'), 'C': b.rpn('B'),
                     'F': b.rpn('ang'), 'O': b.rpn(signed),
                     'X': b.rpn(f'( abs ` {ab} )'),
                     'Y': b.rpn(f'( abs ` {cb} )'),
                     'Z': b.rpn(f'( abs ` {ca} )')},
                    b.ap('df-ang'),
                    b.ap('eqid', {'A': b.rpn(f'( abs ` {ab} )')}),
                    b.ap('eqid', {'A': b.rpn(f'( abs ` {cb} )')}),
                    b.ap('eqid', {'A': b.rpn(f'( abs ` {ca} )')}),
                    b.ap('eqid', {'A': b.rpn(signed)})))

    # |C - B| is |B - C|, and the cosine does not see the angle's sign.
    flip = b.ap('syl2anc', {'ph': b.wff(ph), 'ps': b.wff('C e. CC'),
                            'ch': b.wff('B e. CC'),
                            'th': b.wff(f'( abs ` {cb} ) = ( abs ` {bc} )')},
                mem['C'], mem['B'],
                b.ap('abssub', {'A': b.rpn('C'), 'B': b.rpn('B')}))
    ab_cc = b.ap('subcld', {'ph': b.wff(ph), 'A': b.rpn('A'), 'B': b.rpn('B')},
                 mem['A'], mem['B'])
    cb_cc = b.ap('subcld', {'ph': b.wff(ph), 'A': b.rpn('C'), 'B': b.rpn('B')},
                 mem['C'], mem['B'])
    ab_nz = differs(b, ph, 'A', 'B', mem['A'], mem['B'], unequal['AB'])
    cb_nz = differs(b, ph, 'C', 'B', mem['C'], mem['B'], unequal['CB'])
    quotient = b.ap('divcld', {'ph': b.wff(ph), 'A': b.rpn(cb),
                               'B': b.rpn(ab)}, cb_cc, ab_cc, ab_nz)
    ready = b.ap('jca',
                 {'ph': b.wff(ph),
                  'ps': b.wff(f'( {ab} e. CC /\\ {ab} =/= 0 )'),
                  'ch': b.wff(f'( {cb} e. CC /\\ {cb} =/= 0 )')},
                 b.ap('jca', {'ph': b.wff(ph), 'ps': b.wff(f'{ab} e. CC'),
                              'ch': b.wff(f'{ab} =/= 0')}, ab_cc, ab_nz),
                 b.ap('jca', {'ph': b.wff(ph), 'ps': b.wff(f'{cb} e. CC'),
                              'ch': b.wff(f'{cb} =/= 0')}, cb_cc, cb_nz))
    ang_value = b.ap('syl',
                     {'ph': b.wff(ph),
                      'ps': b.wff(f'( ( {ab} e. CC /\\ {ab} =/= 0 ) '
                                  f'/\\ ( {cb} e. CC /\\ {cb} =/= 0 ) )'),
                      'ch': b.wff(f'{signed} '
                                  f'= ( Im ` ( log ` ( {cb} / {ab} ) ) )')},
                     ready, b.ap('gangval', {'A': b.rpn(ab), 'B': b.rpn(cb)}))
    signed_re = b.ap('eqeltrd',
                     {'ph': b.wff(ph), 'A': b.rpn(signed),
                      'B': b.rpn(f'( Im ` ( log ` ( {cb} / {ab} ) ) )'),
                      'C': b.rpn('RR')},
                     ang_value,
                     b.ap('imcld',
                          {'ph': b.wff(ph),
                           'A': b.rpn(f'( log ` ( {cb} / {ab} ) )')},
                          b.ap('logcld', {'ph': b.wff(ph),
                                          'X': b.rpn(f'( {cb} / {ab} )')},
                               quotient,
                               b.ap('divne0d',
                                    {'ph': b.wff(ph), 'A': b.rpn(cb),
                                     'B': b.rpn(ab)},
                                    cb_cc, ab_cc, cb_nz, ab_nz))))
    unsign = b.ap('eqcomd',
                  {'ph': b.wff(ph),
                   'A': b.rpn(f'( cos ` ( abs ` {signed} ) )'),
                   'B': b.rpn(f'( cos ` {signed} )')},
                  b.ap('syl',
                       {'ph': b.wff(ph), 'ps': b.wff(f'{signed} e. RR'),
                        'ch': b.wff(f'( cos ` ( abs ` {signed} ) ) '
                                    f'= ( cos ` {signed} )')},
                       signed_re,
                       b.ap('gcosabs', {'A': b.rpn(signed)})))
    says = (f'|- ( {ph} -> ( ( abs ` {ca} ) ^ 2 ) = ( ( ( ( abs ` {ab} ) ^ 2 )'
            f' + ( ( abs ` {bc} ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. '
            f'( abs ` {bc} ) ) x. ( cos ` ( abs ` {signed} ) ) ) ) ) )')
    out.append(('glawcos', says, b.ap(
        'eqtrd', {'ph': b.wff(ph), 'A': b.rpn(f'( ( abs ` {ca} ) ^ 2 )'),
                  'B': b.rpn(f'( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {cb} ) '
                             f'^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. '
                             f'( abs ` {cb} ) ) x. ( cos ` {signed} ) ) ) )'),
                  'C': b.rpn(f'( ( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {bc} ) '
                             f'^ 2 ) ) - ( 2 x. ( ( ( abs ` {ab} ) x. '
                             f'( abs ` {bc} ) ) x. '
                             f'( cos ` ( abs ` {signed} ) ) ) ) )')},
        raw,
        b.ap('oveq12d',
             {'ph': b.wff(ph),
              'A': b.rpn(f'( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {cb} ) ^ 2 ) )'),
              'B': b.rpn(f'( ( ( abs ` {ab} ) ^ 2 ) + ( ( abs ` {bc} ) ^ 2 ) )'),
              'C': b.rpn(f'( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. '
                         f'( cos ` {signed} ) ) )'),
              'D': b.rpn(f'( 2 x. ( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. '
                         f'( cos ` ( abs ` {signed} ) ) ) )'),
              'F': b.rpn('-')},
             b.ap('oveq2d', {'ph': b.wff(ph),
                             'A': b.rpn(f'( ( abs ` {cb} ) ^ 2 )'),
                             'B': b.rpn(f'( ( abs ` {bc} ) ^ 2 )'),
                             'C': b.rpn(f'( ( abs ` {ab} ) ^ 2 )'),
                             'F': b.rpn('+')},
                  b.ap('oveq1d', {'ph': b.wff(ph),
                                  'A': b.rpn(f'( abs ` {cb} )'),
                                  'B': b.rpn(f'( abs ` {bc} )'),
                                  'C': b.rpn('2'), 'F': b.rpn('^')}, flip)),
             b.ap('oveq2d',
                  {'ph': b.wff(ph),
                   'A': b.rpn(f'( ( ( abs ` {ab} ) x. ( abs ` {cb} ) ) x. '
                              f'( cos ` {signed} ) )'),
                   'B': b.rpn(f'( ( ( abs ` {ab} ) x. ( abs ` {bc} ) ) x. '
                              f'( cos ` ( abs ` {signed} ) ) )'),
                   'C': b.rpn('2'), 'F': b.rpn('x.')},
                  b.ap('oveq12d',
                       {'ph': b.wff(ph),
                        'A': b.rpn(f'( ( abs ` {ab} ) x. ( abs ` {cb} ) )'),
                        'B': b.rpn(f'( ( abs ` {ab} ) x. ( abs ` {bc} ) )'),
                        'C': b.rpn(f'( cos ` {signed} )'),
                        'D': b.rpn(f'( cos ` ( abs ` {signed} ) )'),
                        'F': b.rpn('x.')},
                       b.ap('oveq2d', {'ph': b.wff(ph),
                                       'A': b.rpn(f'( abs ` {cb} )'),
                                       'B': b.rpn(f'( abs ` {bc} )'),
                                       'C': b.rpn(f'( abs ` {ab} )'),
                                       'F': b.rpn('x.')}, flip),
                       unsign))))))
    b.define('glawcos', says)
    return out


HEAD = """$( geometry, built by elaboration/build-geometry.py.

   What this corpus needs of the plane and set.mm does not state.
   Points are complex numbers, distance is the absolute value of a
   difference, and the angle is the constant definitions.mm introduces,
   so everything here is a theorem rather than an axiom: CC is a model
   and nothing in it has to be assumed.  GEOMETRY.md takes that
   decision and says what it costs. $)

$[ definitions.mm $]

$( `angval` reads a value of the angle by substituting for the two names
   `df-ang` binds, and asks that they be free of what is substituted. They
   appear in no statement here, only inside the proofs. The pairs are
   written one at a time because `$d x y A B` would also hold A and B
   apart, and the lemmas below are applied at terms that share names. $)
$d x y $.
$d x A $.  $d y A $.
$d x B $.  $d y B $.
$d x C $.  $d y C $.
$d x P $.  $d y P $.
$d x Q $.  $d y Q $.
$d x R $.  $d y R $.
$d x S $.  $d y S $.
$d x T $.  $d y T $.
$d x U $.  $d y U $.

"""


def main(argv):
    if len(argv) < 2:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    # The angle is a constant this corpus introduces, so the definitions
    # are read alongside the library: `angval` says what a value of it is,
    # and discharging that needs `df-ang`.
    here = Path(__file__).resolve().parent
    sigs = read_library(argv[1], here / 'auto' / 'definitions.mm')
    b = Builder(sigs)
    print(HEAD, end='')
    for label, statement, proof in law_of_cosines(
            b, angle_size(
                b, angle_symmetry(b, rotation(b, triangle_lemmas(b))))):
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
