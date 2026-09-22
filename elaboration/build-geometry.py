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

This writes to standard output. Where the file goes is `parley/build.py`,
which is also what `parley/labels.py` and `parley/elaborate.py` ask, so the
three cannot drift apart. Run it through `parley/build.py geometry` rather
than redirecting by hand: written to the wrong place it is a file nothing
opens, and the build looks to have worked.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'parley'))

from build import path_of
from compress import compress
from library import Signature
from library import read as read_library
from spell import Builder


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


def cancelling(b, out):
    """Two laws of cosines with the same sides say the same cosine.

    Both sides of the comparison have the shape Z − 2(K·X), where Z is the
    two squares added and K the two sides multiplied. What is wanted is X,
    so Z comes off by `subcan` and the two factors by `mulcan`. K is a
    product of two lengths and is nonzero because neither vertex meets the
    one the angle sits at."""
    ph = ('( ( X e. CC /\\ Y e. CC /\\ Z e. CC ) '
          '/\\ ( K e. CC /\\ K =/= 0 ) )')
    left, right = '( 2 x. ( K x. X ) )', '( 2 x. ( K x. Y ) )'
    three = b.ap('simpl', {'ph': b.wff('( X e. CC /\\ Y e. CC /\\ Z e. CC )'),
                           'ps': b.wff('( K e. CC /\\ K =/= 0 )')})
    mem = {}
    for name, which in (('X', 'simp1'), ('Y', 'simp2'), ('Z', 'simp3')):
        mem[name] = b.ap('syl', {'ph': b.wff(ph),
                                 'ps': b.wff('( X e. CC /\\ Y e. CC '
                                             '/\\ Z e. CC )'),
                                 'ch': b.wff(f'{name} e. CC')},
                         three,
                         b.ap(which, {'ph': b.wff('X e. CC'),
                                      'ps': b.wff('Y e. CC'),
                                      'ch': b.wff('Z e. CC')}))
    pair = b.ap('simpr', {'ph': b.wff('( X e. CC /\\ Y e. CC /\\ Z e. CC )'),
                          'ps': b.wff('( K e. CC /\\ K =/= 0 )')})
    k_cc = b.ap('simpld', {'ph': b.wff(ph), 'ps': b.wff('K e. CC'),
                           'ch': b.wff('K =/= 0')}, pair)
    two = b.ap('a1i', {'ph': b.wff('2 e. CC'), 'ps': b.wff(ph)}, '2cn')
    two_nz = b.ap('a1i', {'ph': b.wff('2 =/= 0'), 'ps': b.wff(ph)}, '2ne0')

    # Z comes off first, then the 2, then K.
    drops_z = b.ap('syl3anc',
                   {'ph': b.wff(ph), 'ps': b.wff('Z e. CC'),
                    'ch': b.wff(f'{left} e. CC'), 'th': b.wff(f'{right} e. CC'),
                    'ta': b.wff(f'( ( Z - {left} ) = ( Z - {right} ) '
                                f'<-> {left} = {right} )')},
                   mem['Z'],
                   b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('2'),
                                   'B': b.rpn('( K x. X )')}, two,
                        b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('K'),
                                        'B': b.rpn('X')}, k_cc, mem['X'])),
                   b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('2'),
                                   'B': b.rpn('( K x. Y )')}, two,
                        b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('K'),
                                        'B': b.rpn('Y')}, k_cc, mem['Y'])),
                   b.ap('subcan', {'A': b.rpn('Z'), 'B': b.rpn(left),
                                   'C': b.rpn(right)}))
    drops_two = b.ap('syl3anc',
                     {'ph': b.wff(ph), 'ps': b.wff('( K x. X ) e. CC'),
                      'ch': b.wff('( K x. Y ) e. CC'),
                      'th': b.wff('( 2 e. CC /\\ 2 =/= 0 )'),
                      'ta': b.wff(f'( {left} = {right} '
                                  '<-> ( K x. X ) = ( K x. Y ) )')},
                     b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('K'),
                                     'B': b.rpn('X')}, k_cc, mem['X']),
                     b.ap('mulcld', {'ph': b.wff(ph), 'A': b.rpn('K'),
                                     'B': b.rpn('Y')}, k_cc, mem['Y']),
                     b.ap('jca', {'ph': b.wff(ph), 'ps': b.wff('2 e. CC'),
                                  'ch': b.wff('2 =/= 0')}, two, two_nz),
                     b.ap('mulcan', {'A': b.rpn('( K x. X )'),
                                     'B': b.rpn('( K x. Y )'),
                                     'C': b.rpn('2')}))
    drops_k = b.ap('syl3anc',
                   {'ph': b.wff(ph), 'ps': b.wff('X e. CC'),
                    'ch': b.wff('Y e. CC'),
                    'th': b.wff('( K e. CC /\\ K =/= 0 )'),
                    'ta': b.wff('( ( K x. X ) = ( K x. Y ) <-> X = Y )')},
                   mem['X'], mem['Y'], pair,
                   b.ap('mulcan', {'A': b.rpn('X'), 'B': b.rpn('Y'),
                                   'C': b.rpn('K')}))
    says = (f'|- ( {ph} -> ( ( Z - {left} ) = ( Z - {right} ) -> X = Y ) )')
    out.append(('gcoscan', says, b.ap(
        'sylibd', {'ph': b.wff(ph),
                   'ps': b.wff(f'( Z - {left} ) = ( Z - {right} )'),
                   'ch': b.wff('( K x. X ) = ( K x. Y )'),
                   'th': b.wff('X = Y')},
        b.ap('sylibd', {'ph': b.wff(ph),
                        'ps': b.wff(f'( Z - {left} ) = ( Z - {right} )'),
                        'ch': b.wff(f'{left} = {right}'),
                        'th': b.wff('( K x. X ) = ( K x. Y )')},
             b.ap('biimpd', {'ph': b.wff(ph),
                             'ps': b.wff(f'( Z - {left} ) = ( Z - {right} )'),
                             'ch': b.wff(f'{left} = {right}')}, drops_z),
             drops_two),
        drops_k)))
    b.define('gcoscan', says)

    # Going back from the cosine to the angle, which is possible only
    # because the angle the corpus writes is unsigned: cosine is one to
    # one on 0 to pi and on nothing wider.
    nz = '( ( A e. CC /\\ A =/= 0 ) /\\ ( B e. CC /\\ B =/= 0 ) )'
    nz2 = '( ( C e. CC /\\ C =/= 0 ) /\\ ( D e. CC /\\ D =/= 0 ) )'
    both = f'( {nz} /\\ {nz2} )'
    one, two = '( abs ` ( A ang B ) )', '( abs ` ( C ang D ) )'
    says = (f'|- ( {both} -> ( ( cos ` {one} ) = ( cos ` {two} ) '
            f'-> {one} = {two} ) )')
    out.append(('gangeq', says, b.ap(
        'biimprd', {'ph': b.wff(both), 'ps': b.wff(f'{one} = {two}'),
                    'ch': b.wff(f'( cos ` {one} ) = ( cos ` {two} )')},
        b.ap('syl2anc',
             {'ph': b.wff(both), 'ps': b.wff(f'{one} e. ( 0 [,] _pi )'),
              'ch': b.wff(f'{two} e. ( 0 [,] _pi )'),
              'th': b.wff(f'( {one} = {two} <-> ( cos ` {one} ) '
                          f'= ( cos ` {two} ) )')},
             b.ap('syl', {'ph': b.wff(both), 'ps': b.wff(nz),
                          'ch': b.wff(f'{one} e. ( 0 [,] _pi )')},
                  b.ap('simpl', {'ph': b.wff(nz), 'ps': b.wff(nz2)}),
                  b.ap('gangrange', {'A': b.rpn('A'), 'B': b.rpn('B')})),
             b.ap('syl', {'ph': b.wff(both), 'ps': b.wff(nz2),
                          'ch': b.wff(f'{two} e. ( 0 [,] _pi )')},
                  b.ap('simpr', {'ph': b.wff(nz), 'ps': b.wff(nz2)}),
                  b.ap('gangrange', {'A': b.rpn('C'), 'B': b.rpn('D')})),
             b.ap('cos11', {'A': b.rpn(one), 'B': b.rpn(two)})))))
    b.define('gangeq', says)
    return out


def side_angle_side(b, out):
    """Two sides and the angle between them fix the triangle.

    An axiom in Euclid and in Hilbert, because a synthetic geometry has no
    coordinates to compute with and congruence has to be stipulated. Over
    CC it is a theorem, and this is the proof: the law of cosines at each
    of the three vertices, six applications in all, which are three cyclic
    rotations of `glawcos` in each triangle.

    The third side comes first, from the law at the given angle's vertex,
    since equal sides and equal cosines make equal squares and a length is
    not negative. With all three sides equal the other two angles follow
    the other way round: the law at each of the remaining vertices has the
    same sides on both sides of the comparison, so `gcoscan` leaves the
    cosines equal and `gangeq` turns that back into the angles."""
    first = '( P e. CC /\\ Q e. CC /\\ R e. CC )'
    second = '( S e. CC /\\ T e. CC /\\ U e. CC )'
    pts = f'( {first} /\\ {second} )'
    tri1, tri2 = triangle('P', 'Q', 'R'), triangle('S', 'T', 'U')

    def side(x, y):
        return f'( abs ` ( {x} - {y} ) )'

    def at(x, y, z):
        """The corpus's unsigned angle at y, between the rays to x and z."""
        return f'( abs ` ( ( {x} - {y} ) ang ( {z} - {y} ) ) )'

    same_pq = f'{side("P", "Q")} = {side("S", "T")}'
    same_qr = f'{side("Q", "R")} = {side("T", "U")}'
    same_rp = f'{side("R", "P")} = {side("U", "S")}'
    ang_q = f'{at("P", "Q", "R")} = {at("S", "T", "U")}'
    ang_r = f'{at("Q", "R", "P")} = {at("T", "U", "S")}'
    ang_p = f'{at("R", "P", "Q")} = {at("U", "S", "T")}'

    # The antecedents nest to the left, so a fact proved under a prefix is
    # carried out to the whole by one `adantr` for each later one.
    levels = [pts, tri1, tri2, same_pq, ang_q, same_qr]
    ws = [levels[0]]
    for one in levels[1:]:
        ws.append(f'( {ws[-1]} /\\ {one} )')
    whole = ws[-1]

    def lift(claim, proof, frm):
        for i in range(frm, len(levels) - 1):
            proof = b.ap('adantr', {'ph': b.wff(ws[i]), 'ps': b.wff(claim),
                                    'ch': b.wff(levels[i + 1])}, proof)
        return proof

    def given(i):
        """The i-th antecedent, as a fact of the whole."""
        return lift(levels[i],
                    b.ap('simpr', {'ph': b.wff(ws[i - 1]),
                                   'ps': b.wff(levels[i])}), i)

    mem = {}
    for name, which, half in (('P', 'simp1', 'simpl'), ('Q', 'simp2', 'simpl'),
                              ('R', 'simp3', 'simpl'), ('S', 'simp1', 'simpr'),
                              ('T', 'simp2', 'simpr'), ('U', 'simp3', 'simpr')):
        side_of = first if half == 'simpl' else second
        names = ('P', 'Q', 'R') if half == 'simpl' else ('S', 'T', 'U')
        mem[name] = lift(f'{name} e. CC', b.ap(
            'syl', {'ph': b.wff(pts), 'ps': b.wff(side_of),
                    'ch': b.wff(f'{name} e. CC')},
            b.ap(half, {'ph': b.wff(first), 'ps': b.wff(second)}),
            b.ap(which, {'ph': b.wff(f'{names[0]} e. CC'),
                         'ps': b.wff(f'{names[1]} e. CC'),
                         'ch': b.wff(f'{names[2]} e. CC')})), 0)

    def apart_of(which, x, y, z, level):
        """The three disequalities a triangle states, as facts of the whole.

        The predicate is ((( x!=y & y!=z ) & x!=z ) & not collinear), so
        the three come off by taking the left conjunct twice and then the
        halves; the reversed ones the rotations want come off `flipped`."""
        inner = (f'( ( -. {x} = {y} /\\ -. {y} = {z} ) /\\ -. {x} = {z} )')
        pair = f'( -. {x} = {y} /\\ -. {y} = {z} )'
        held = given(level)
        cut = b.ap('simpld',
                   {'ph': b.wff(whole), 'ps': b.wff(inner),
                    'ch': b.wff(f'-. ( ( {z} - {x} ) / ( {y} - {x} ) ) '
                                f'e. RR')}, held)
        two = b.ap('simpld', {'ph': b.wff(whole), 'ps': b.wff(pair),
                              'ch': b.wff(f'-. {x} = {z}')}, cut)
        out = {(x, z): b.ap('simprd', {'ph': b.wff(whole), 'ps': b.wff(pair),
                                       'ch': b.wff(f'-. {x} = {z}')}, cut),
               (x, y): b.ap('simpld', {'ph': b.wff(whole),
                                       'ps': b.wff(f'-. {x} = {y}'),
                                       'ch': b.wff(f'-. {y} = {z}')}, two),
               (y, z): b.ap('simprd', {'ph': b.wff(whole),
                                       'ps': b.wff(f'-. {x} = {y}'),
                                       'ch': b.wff(f'-. {y} = {z}')}, two)}
        for (a, c), proof in list(out.items()):
            out[(c, a)] = flipped(b, whole, a, c, proof)
        del which
        return out

    ne1 = apart_of('tri1', 'P', 'Q', 'R', 1)
    ne2 = apart_of('tri2', 'S', 'T', 'U', 2)

    def law(x, y, z, ne):
        """`glawcos` at y: the side opposite y from the two sides at it."""
        return b.ap(
            'syl', {'ph': b.wff(whole),
                    'ps': b.wff(f'( ( {x} e. CC /\\ {y} e. CC /\\ {z} e. CC ) '
                                f'/\\ ( -. {x} = {y} /\\ -. {z} = {y} ) )'),
                    'ch': b.wff(f'( {side(z, x)} ^ 2 ) = ( ( ( {side(x, y)} '
                                f'^ 2 ) + ( {side(y, z)} ^ 2 ) ) - ( 2 x. ( '
                                f'( {side(x, y)} x. {side(y, z)} ) x. ( cos ` '
                                f'{at(x, y, z)} ) ) ) )')},
            b.ap('jca', {'ph': b.wff(whole),
                         'ps': b.wff(f'( {x} e. CC /\\ {y} e. CC '
                                     f'/\\ {z} e. CC )'),
                         'ch': b.wff(f'( -. {x} = {y} /\\ -. {z} = {y} )')},
                 b.ap('3jca', {'ph': b.wff(whole), 'ps': b.wff(f'{x} e. CC'),
                               'ch': b.wff(f'{y} e. CC'),
                               'th': b.wff(f'{z} e. CC')},
                      mem[x], mem[y], mem[z]),
                 b.ap('jca', {'ph': b.wff(whole),
                              'ps': b.wff(f'-. {x} = {y}'),
                              'ch': b.wff(f'-. {z} = {y}')},
                      ne[(x, y)], ne[(z, y)])),
            b.ap('glawcos', {'A': b.rpn(x), 'B': b.rpn(y), 'C': b.rpn(z)}))

    def right_hand(a1, a2, b1, b2, x1, x2, ea, eb, ex_):
        """The two right-hand sides agree, component by component."""
        squares = b.ap(
            'oveq12d', {'ph': b.wff(whole), 'A': b.rpn(f'( {a1} ^ 2 )'),
                        'B': b.rpn(f'( {a2} ^ 2 )'),
                        'C': b.rpn(f'( {b1} ^ 2 )'),
                        'D': b.rpn(f'( {b2} ^ 2 )'), 'F': b.rpn('+')},
            b.ap('oveq1d', {'ph': b.wff(whole), 'A': b.rpn(a1), 'B': b.rpn(a2),
                            'C': b.rpn('2'), 'F': b.rpn('^')}, ea),
            b.ap('oveq1d', {'ph': b.wff(whole), 'A': b.rpn(b1), 'B': b.rpn(b2),
                            'C': b.rpn('2'), 'F': b.rpn('^')}, eb))
        product = b.ap(
            'oveq12d', {'ph': b.wff(whole), 'A': b.rpn(f'( {a1} x. {b1} )'),
                        'B': b.rpn(f'( {a2} x. {b2} )'), 'C': b.rpn(x1),
                        'D': b.rpn(x2), 'F': b.rpn('x.')},
            b.ap('oveq12d', {'ph': b.wff(whole), 'A': b.rpn(a1),
                             'B': b.rpn(a2), 'C': b.rpn(b1), 'D': b.rpn(b2),
                             'F': b.rpn('x.')}, ea, eb),
            ex_)
        return b.ap(
            'oveq12d',
            {'ph': b.wff(whole),
             'A': b.rpn(f'( ( {a1} ^ 2 ) + ( {b1} ^ 2 ) )'),
             'B': b.rpn(f'( ( {a2} ^ 2 ) + ( {b2} ^ 2 ) )'),
             'C': b.rpn(f'( 2 x. ( ( {a1} x. {b1} ) x. {x1} ) )'),
             'D': b.rpn(f'( 2 x. ( ( {a2} x. {b2} ) x. {x2} ) )'),
             'F': b.rpn('-')},
            squares,
            b.ap('oveq2d', {'ph': b.wff(whole),
                            'A': b.rpn(f'( ( {a1} x. {b1} ) x. {x1} )'),
                            'B': b.rpn(f'( ( {a2} x. {b2} ) x. {x2} )'),
                            'C': b.rpn('2'), 'F': b.rpn('x.')}, product))

    def cosines(equal, one, two):
        """An equality of angles, read through cosine."""
        return b.ap('fveq2d', {'ph': b.wff(whole), 'A': b.rpn(one),
                               'B': b.rpn(two), 'F': b.rpn('cos')}, equal)

    # The third side. Equal sides and an equal angle make equal squares,
    # and a length is not negative, so the sides themselves are equal.
    squares_rp = b.ap(
        '3eqtr4d', {'ph': b.wff(whole),
                    'A': b.rpn(f'( ( ( {side("P", "Q")} ^ 2 ) + '
                               f'( {side("Q", "R")} ^ 2 ) ) - ( 2 x. ( ( '
                               f'{side("P", "Q")} x. {side("Q", "R")} ) x. '
                               f'( cos ` {at("P", "Q", "R")} ) ) ) )'),
                    'B': b.rpn(f'( ( ( {side("S", "T")} ^ 2 ) + '
                               f'( {side("T", "U")} ^ 2 ) ) - ( 2 x. ( ( '
                               f'{side("S", "T")} x. {side("T", "U")} ) x. '
                               f'( cos ` {at("S", "T", "U")} ) ) ) )'),
                    'C': b.rpn(f'( {side("R", "P")} ^ 2 )'),
                    'D': b.rpn(f'( {side("U", "S")} ^ 2 )')},
        right_hand(side('P', 'Q'), side('S', 'T'),
                   side('Q', 'R'), side('T', 'U'),
                   f'( cos ` {at("P", "Q", "R")} )',
                   f'( cos ` {at("S", "T", "U")} )',
                   given(3), given(5),
                   cosines(given(4), at('P', 'Q', 'R'), at('S', 'T', 'U'))),
        law('P', 'Q', 'R', ne1), law('S', 'T', 'U', ne2))
    third = b.ap(
        'mpbid', {'ph': b.wff(whole),
                  'ps': b.wff(f'( {side("R", "P")} ^ 2 ) '
                              f'= ( {side("U", "S")} ^ 2 )'),
                  'ch': b.wff(same_rp)},
        squares_rp,
        b.ap('syl2anc',
             {'ph': b.wff(whole),
              'ps': b.wff(f'( {side("R", "P")} e. RR '
                          f'/\\ 0 <_ {side("R", "P")} )'),
              'ch': b.wff(f'( {side("U", "S")} e. RR '
                          f'/\\ 0 <_ {side("U", "S")} )'),
              'th': b.wff(f'( ( {side("R", "P")} ^ 2 ) '
                          f'= ( {side("U", "S")} ^ 2 ) <-> {same_rp} )')},
             *[b.ap('jca', {'ph': b.wff(whole),
                            'ps': b.wff(f'{side(x, y)} e. RR'),
                            'ch': b.wff(f'0 <_ {side(x, y)}')},
                    b.ap('abscld', {'ph': b.wff(whole),
                                    'A': b.rpn(f'( {x} - {y} )')},
                         b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(x),
                                         'B': b.rpn(y)}, mem[x], mem[y])),
                    b.ap('absge0d', {'ph': b.wff(whole),
                                     'A': b.rpn(f'( {x} - {y} )')},
                         b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(x),
                                         'B': b.rpn(y)}, mem[x], mem[y])))
               for x, y in (('R', 'P'), ('U', 'S'))],
             b.ap('sq11', {'A': b.rpn(side('R', 'P')),
                           'B': b.rpn(side('U', 'S'))})))
    def length_cc(x, y):
        return b.ap('recnd', {'ph': b.wff(whole), 'A': b.rpn(side(x, y))},
                    b.ap('abscld', {'ph': b.wff(whole),
                                    'A': b.rpn(f'( {x} - {y} )')},
                         b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(x),
                                         'B': b.rpn(y)}, mem[x], mem[y])))

    def length_nz(x, y, ne):
        return b.ap('absne0d', {'ph': b.wff(whole),
                                'A': b.rpn(f'( {x} - {y} )')},
                    b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(x),
                                    'B': b.rpn(y)}, mem[x], mem[y]),
                    differs(b, whole, x, y, mem[x], mem[y], ne[(x, y)]))

    def angle_cc(x, y, z, ne):
        """The unsigned angle is a number, which `gcoscan` needs of it."""
        holds = b.ap(
            'jca', {'ph': b.wff(whole),
                    'ps': b.wff(f'( ( {x} - {y} ) e. CC '
                                f'/\\ ( {x} - {y} ) =/= 0 )'),
                    'ch': b.wff(f'( ( {z} - {y} ) e. CC '
                                f'/\\ ( {z} - {y} ) =/= 0 )')},
            *[b.ap('jca', {'ph': b.wff(whole),
                           'ps': b.wff(f'( {a} - {y} ) e. CC'),
                           'ch': b.wff(f'( {a} - {y} ) =/= 0')},
                   b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(a),
                                   'B': b.rpn(y)}, mem[a], mem[y]),
                   differs(b, whole, a, y, mem[a], mem[y], ne[(a, y)]))
              for a in (x, z)])
        inside = b.ap(
            'syl', {'ph': b.wff(whole),
                    'ps': b.wff(f'( ( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) '
                                f'=/= 0 ) /\\ ( ( {z} - {y} ) e. CC /\\ '
                                f'( {z} - {y} ) =/= 0 ) )'),
                    'ch': b.wff(f'{at(x, y, z)} e. ( 0 [,] _pi )')},
            holds, b.ap('gangrange', {'A': b.rpn(f'( {x} - {y} )'),
                                      'B': b.rpn(f'( {z} - {y} )')}))
        return b.ap(
            'recnd', {'ph': b.wff(whole), 'A': b.rpn(at(x, y, z))},
            b.ap('simp1d', {'ph': b.wff(whole),
                            'ps': b.wff(f'{at(x, y, z)} e. RR'),
                            'ch': b.wff(f'0 <_ {at(x, y, z)}'),
                            'th': b.wff(f'{at(x, y, z)} <_ _pi')},
                 b.ap('mpbid', {'ph': b.wff(whole),
                                'ps': b.wff(f'{at(x, y, z)} e. ( 0 [,] _pi )'),
                                'ch': b.wff(f'( {at(x, y, z)} e. RR /\\ 0 <_ '
                                            f'{at(x, y, z)} /\\ '
                                            f'{at(x, y, z)} <_ _pi )')},
                      inside,
                      b.ap('syl2anc',
                           {'ph': b.wff(whole), 'ps': b.wff('0 e. RR'),
                            'ch': b.wff('_pi e. RR'),
                            'th': b.wff(f'( {at(x, y, z)} e. ( 0 [,] _pi ) '
                                        f'<-> ( {at(x, y, z)} e. RR /\\ 0 <_ '
                                        f'{at(x, y, z)} /\\ {at(x, y, z)} '
                                        f'<_ _pi ) )')},
                           b.ap('a1i', {'ph': b.wff('0 e. RR'),
                                        'ps': b.wff(whole)}, '0re'),
                           b.ap('a1i', {'ph': b.wff('_pi e. RR'),
                                        'ps': b.wff(whole)}, 'pire'),
                           b.ap('elicc2', {'A': b.rpn('0'), 'B': b.rpn('_pi'),
                                           'C': b.rpn(at(x, y, z))})))))

    def angle_equal(x, y, z, x2, y2, z2, e_opp, e_a, e_b):
        """The angle at y is the angle at y2, all three sides agreeing.

        Both laws have the same two sides at the vertex and the same side
        opposite it, so what is left once `gcoscan` has taken the squares
        and the factors off is the cosine, and `gangeq` is the way back."""
        z_of = f'( ( {side(x, y)} ^ 2 ) + ( {side(y, z)} ^ 2 ) )'
        k_of = f'( {side(x, y)} x. {side(y, z)} )'
        cos1, cos2 = f'( cos ` {at(x, y, z)} )', f'( cos ` {at(x2, y2, z2)} )'
        # The two right-hand sides are equal because the sides opposite
        # the vertex are, and then the second is rewritten in the first's
        # own lengths so that only the cosine differs.
        agree = b.ap(
            '3eqtr3d',
            {'ph': b.wff(whole), 'A': b.rpn(f'( {side(z, x)} ^ 2 )'),
             'B': b.rpn(f'( {side(z2, x2)} ^ 2 )'),
             'C': b.rpn(f'( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) )'),
             'D': b.rpn(f'( ( ( {side(x2, y2)} ^ 2 ) + ( {side(y2, z2)} ^ 2 ) '
                        f') - ( 2 x. ( ( {side(x2, y2)} x. {side(y2, z2)} ) '
                        f'x. {cos2} ) ) )')},
            b.ap('oveq1d', {'ph': b.wff(whole), 'A': b.rpn(side(z, x)),
                            'B': b.rpn(side(z2, x2)), 'C': b.rpn('2'),
                            'F': b.rpn('^')}, e_opp),
            law(x, y, z, ne1), law(x2, y2, z2, ne2))
        rewritten = right_hand(
            side(x2, y2), side(x, y), side(y2, z2), side(y, z), cos2, cos2,
            b.ap('eqcomd', {'ph': b.wff(whole), 'A': b.rpn(side(x, y)),
                            'B': b.rpn(side(x2, y2))}, e_a),
            b.ap('eqcomd', {'ph': b.wff(whole), 'A': b.rpn(side(y, z)),
                            'B': b.rpn(side(y2, z2))}, e_b),
            b.ap('a1i', {'ph': b.wff(f'{cos2} = {cos2}'), 'ps': b.wff(whole)},
                 b.ap('eqid', {'A': b.rpn(cos2)})))
        lined = b.ap(
            'eqtrd', {'ph': b.wff(whole),
                      'A': b.rpn(f'( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) )'),
                      'B': b.rpn(f'( ( ( {side(x2, y2)} ^ 2 ) + '
                                 f'( {side(y2, z2)} ^ 2 ) ) - ( 2 x. ( ( '
                                 f'{side(x2, y2)} x. {side(y2, z2)} ) x. '
                                 f'{cos2} ) ) )'),
                      'C': b.rpn(f'( {z_of} - ( 2 x. ( {k_of} x. {cos2} ) ) )')},
            agree, rewritten)
        k_cc = b.ap('mulcld', {'ph': b.wff(whole), 'A': b.rpn(side(x, y)),
                               'B': b.rpn(side(y, z))},
                    length_cc(x, y), length_cc(y, z))
        k_nz = b.ap('syl', {'ph': b.wff(whole),
                            'ps': b.wff(f'( ( {side(x, y)} e. CC /\\ '
                                        f'{side(x, y)} =/= 0 ) /\\ ( '
                                        f'{side(y, z)} e. CC /\\ '
                                        f'{side(y, z)} =/= 0 ) )'),
                            'ch': b.wff(f'{k_of} =/= 0')},
                    b.ap('jca', {'ph': b.wff(whole),
                                 'ps': b.wff(f'( {side(x, y)} e. CC /\\ '
                                             f'{side(x, y)} =/= 0 )'),
                                 'ch': b.wff(f'( {side(y, z)} e. CC /\\ '
                                             f'{side(y, z)} =/= 0 )')},
                         b.ap('jca', {'ph': b.wff(whole),
                                      'ps': b.wff(f'{side(x, y)} e. CC'),
                                      'ch': b.wff(f'{side(x, y)} =/= 0')},
                              length_cc(x, y), length_nz(x, y, ne1)),
                         b.ap('jca', {'ph': b.wff(whole),
                                      'ps': b.wff(f'{side(y, z)} e. CC'),
                                      'ch': b.wff(f'{side(y, z)} =/= 0')},
                              length_cc(y, z), length_nz(y, z, ne1))),
                    b.ap('mulne0', {'A': b.rpn(side(x, y)),
                                    'B': b.rpn(side(y, z))}))
        equal_cos = b.ap(
            'mpd', {'ph': b.wff(whole),
                    'ps': b.wff(f'( {z_of} - ( 2 x. ( {k_of} x. {cos1} ) ) ) '
                                f'= ( {z_of} - ( 2 x. ( {k_of} x. {cos2} ) ) )'),
                    'ch': b.wff(f'{cos1} = {cos2}')},
            lined,
            b.ap('syl', {'ph': b.wff(whole),
                         'ps': b.wff(f'( ( {cos1} e. CC /\\ {cos2} e. CC /\\ '
                                     f'{z_of} e. CC ) /\\ ( {k_of} e. CC /\\ '
                                     f'{k_of} =/= 0 ) )'),
                         'ch': b.wff(f'( ( {z_of} - ( 2 x. ( {k_of} x. {cos1} '
                                     f') ) ) = ( {z_of} - ( 2 x. ( {k_of} x. '
                                     f'{cos2} ) ) ) -> {cos1} = {cos2} )')},
                 b.ap('jca', {'ph': b.wff(whole),
                              'ps': b.wff(f'( {cos1} e. CC /\\ {cos2} e. CC '
                                          f'/\\ {z_of} e. CC )'),
                              'ch': b.wff(f'( {k_of} e. CC /\\ '
                                          f'{k_of} =/= 0 )')},
                      b.ap('3jca', {'ph': b.wff(whole),
                                    'ps': b.wff(f'{cos1} e. CC'),
                                    'ch': b.wff(f'{cos2} e. CC'),
                                    'th': b.wff(f'{z_of} e. CC')},
                           b.ap('syl', {'ph': b.wff(whole),
                                        'ps': b.wff(f'{at(x, y, z)} e. CC'),
                                        'ch': b.wff(f'{cos1} e. CC')},
                                angle_cc(x, y, z, ne1),
                                b.ap('coscl', {'A': b.rpn(at(x, y, z))})),
                           b.ap('syl', {'ph': b.wff(whole),
                                        'ps': b.wff(f'{at(x2, y2, z2)} e. CC'),
                                        'ch': b.wff(f'{cos2} e. CC')},
                                angle_cc(x2, y2, z2, ne2),
                                b.ap('coscl', {'A': b.rpn(at(x2, y2, z2))})),
                           b.ap('addcld', {'ph': b.wff(whole),
                                           'A': b.rpn(f'( {side(x, y)} ^ 2 )'),
                                           'B': b.rpn(f'( {side(y, z)} ^ 2 )')},
                                b.ap('sqcld', {'ph': b.wff(whole),
                                               'A': b.rpn(side(x, y))},
                                     length_cc(x, y)),
                                b.ap('sqcld', {'ph': b.wff(whole),
                                               'A': b.rpn(side(y, z))},
                                     length_cc(y, z)))),
                      b.ap('jca', {'ph': b.wff(whole),
                                   'ps': b.wff(f'{k_of} e. CC'),
                                   'ch': b.wff(f'{k_of} =/= 0')},
                           k_cc, k_nz)),
                 b.ap('gcoscan', {'X': b.rpn(cos1), 'Y': b.rpn(cos2),
                                  'Z': b.rpn(z_of), 'K': b.rpn(k_of)})))
        ready = b.ap(
            'jca', {'ph': b.wff(whole),
                    'ps': b.wff(f'( ( ( {x} - {y} ) e. CC /\\ ( {x} - {y} ) '
                                f'=/= 0 ) /\\ ( ( {z} - {y} ) e. CC /\\ '
                                f'( {z} - {y} ) =/= 0 ) )'),
                    'ch': b.wff(f'( ( ( {x2} - {y2} ) e. CC /\\ ( {x2} - {y2} )'
                                f' =/= 0 ) /\\ ( ( {z2} - {y2} ) e. CC /\\ '
                                f'( {z2} - {y2} ) =/= 0 ) )')},
            *[b.ap('jca', {'ph': b.wff(whole),
                           'ps': b.wff(f'( ( {a} - {v} ) e. CC /\\ '
                                       f'( {a} - {v} ) =/= 0 )'),
                           'ch': b.wff(f'( ( {c} - {v} ) e. CC /\\ '
                                       f'( {c} - {v} ) =/= 0 )')},
                   *[b.ap('jca', {'ph': b.wff(whole),
                                  'ps': b.wff(f'( {e} - {v} ) e. CC'),
                                  'ch': b.wff(f'( {e} - {v} ) =/= 0')},
                          b.ap('subcld', {'ph': b.wff(whole), 'A': b.rpn(e),
                                          'B': b.rpn(v)}, mem[e], mem[v]),
                          differs(b, whole, e, v, mem[e], mem[v], nn[(e, v)]))
                     for e in (a, c)])
              for a, v, c, nn in ((x, y, z, ne1), (x2, y2, z2, ne2))])
        return b.ap(
            'mpd', {'ph': b.wff(whole), 'ps': b.wff(f'{cos1} = {cos2}'),
                    'ch': b.wff(f'{at(x, y, z)} = {at(x2, y2, z2)}')},
            equal_cos,
            b.ap('syl', {'ph': b.wff(whole),
                         'ps': b.wff(f'( ( ( ( {x} - {y} ) e. CC /\\ '
                                     f'( {x} - {y} ) =/= 0 ) /\\ ( ( {z} - {y}'
                                     f' ) e. CC /\\ ( {z} - {y} ) =/= 0 ) ) '
                                     f'/\\ ( ( ( {x2} - {y2} ) e. CC /\\ '
                                     f'( {x2} - {y2} ) =/= 0 ) /\\ ( ( {z2} - '
                                     f'{y2} ) e. CC /\\ ( {z2} - {y2} ) '
                                     f'=/= 0 ) ) )'),
                         'ch': b.wff(f'( {cos1} = {cos2} -> {at(x, y, z)} '
                                     f'= {at(x2, y2, z2)} )')},
                 ready,
                 b.ap('gangeq', {'A': b.rpn(f'( {x} - {y} )'),
                                 'B': b.rpn(f'( {z} - {y} )'),
                                 'C': b.rpn(f'( {x2} - {y2} )'),
                                 'D': b.rpn(f'( {z2} - {y2} )')})))

    at_r = angle_equal('Q', 'R', 'P', 'T', 'U', 'S',
                       given(3), given(5), third)
    at_p = angle_equal('R', 'P', 'Q', 'U', 'S', 'T',
                       given(5), third, given(3))

    congruent = b.ap(
        'jca', {'ph': b.wff(whole),
                'ps': b.wff(f'( ( ( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} )'
                            f' /\\ {ang_q} ) /\\ {ang_r} )'),
                'ch': b.wff(ang_p)},
        b.ap('jca', {'ph': b.wff(whole),
                     'ps': b.wff(f'( ( ( {same_pq} /\\ {same_qr} ) /\\ '
                                 f'{same_rp} ) /\\ {ang_q} )'),
                     'ch': b.wff(ang_r)},
             b.ap('jca', {'ph': b.wff(whole),
                          'ps': b.wff(f'( ( {same_pq} /\\ {same_qr} ) /\\ '
                                      f'{same_rp} )'),
                          'ch': b.wff(ang_q)},
                  b.ap('jca31', {'ph': b.wff(whole), 'ps': b.wff(same_pq),
                                 'ch': b.wff(same_qr),
                                 'th': b.wff(same_rp)},
                       given(3), given(5), third),
                  given(4)),
             at_r),
        at_p)

    # The six antecedents come off one at a time, outermost last.
    proof, claim = congruent, (
        f'( ( ( ( ( {same_pq} /\\ {same_qr} ) /\\ {same_rp} ) /\\ {ang_q} ) '
        f'/\\ {ang_r} ) /\\ {ang_p} )')
    for i in range(len(levels) - 1, 0, -1):
        proof = b.ap('ex', {'ph': b.wff(ws[i - 1]), 'ps': b.wff(levels[i]),
                            'ch': b.wff(claim)}, proof)
        claim = f'( {levels[i]} -> {claim} )'
    says = f'|- ( {pts} -> {claim} )'
    out.append(('gsas', says, proof))
    b.define('gsas', says)
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
    sigs = read_library(argv[1], path_of('definitions'))
    b = Builder(sigs)
    made = {}
    print(HEAD, end='')
    for label, statement, proof in side_angle_side(
            b, cancelling(
                b, law_of_cosines(
                    b, angle_size(
                        b, angle_symmetry(
                            b, rotation(b, triangle_lemmas(b))))))):
        print(f'  {label} $p {statement} $=')
        # Compressed, as `parley/elaborate.py` writes its proofs. These
        # lemmas lean on each other, so a label written above is one a
        # proof below may take, and the library does not hold it; what it
        # takes is the variables of its own statement, which is what the
        # signature below records.
        mandatory = sorted({b.flabel[t] for t in statement.split()
                            if t in b.flabel},
                           key=lambda one: b.forder[one])
        said = compress(proof, mandatory, {**sigs, **made})
        made[label] = Signature(label, '$p', statement.split(),
                                [('class', v) for v in mandatory])
        line = '   '
        for token in said.split():
            if len(line) + len(token) > 76:
                print(line)
                line = '   '
            line += ' ' + token
        print(f'{line} $.')
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
