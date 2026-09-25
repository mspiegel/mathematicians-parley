#!/usr/bin/env python3
"""Check that `declines.py` still finds a decline nobody asked about.

`test_check.py` does this for the checker and `test_elaborate.py` for the
elaborator. This one plants the shapes the declines stage looks for, each in
a few lines of its own, and requires that the stage reports every one of
them and says nothing about the ways of asking that are right.

Each shape here was found in the tree before the stage could see it: a
decline bound to a name and asked `is None`, stored as a fact in a dict,
written into an f-string, unpacked as if it were a tuple, spread with `*`,
or reached through another file's function.

Usage:  parley/test_declines.py
"""
import sys
import tempfile
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import declines

# A function that declines, which every case below calls.
DECLINER = '''
def f(x):
    if x:
        return Declined('no')
    return x
'''

# Each: what it is, the source, what declines in the other files by module
# name, and whether the stage must report it.
CASES = [
    ('a decline passed straight to a call', '''
     def g():
         return seq(f(1))
     ''', {}, True),

    ('a decline bound to a name and passed on', '''
     def g():
         made = f(1)
         return seq(made)
     ''', {}, True),

    ('a decline asked `is None` and passed on', '''
     def g():
         made = f(1)
         if made is None:
             return None
         return seq(made)
     ''', {}, True),

    ('a decline stored in a dictionary', '''
     def g(facts):
         made = f(1)
         facts['k'] = made
     ''', {}, True),

    ('a decline written into an f-string', '''
     def g():
         return f'{f(1)} cv'
     ''', {}, True),

    ('a decline unpacked as a tuple', '''
     def g():
         a, b = f(1)
         return a
     ''', {}, True),

    ('a decline spread into a call', '''
     def g():
         return seq(*f(1))
     ''', {}, True),

    ('a function giving back what it asked about declines', '''
     def h():
         where = f(1)
         if declined(where):
             return where
         return where
     def g():
         return seq(h())
     ''', {}, True),

    ('a decline from another file, called on what is not self', '''
     def g(work):
         return seq(work.normalize(1))
     ''', {'normal': frozenset({'normalize'})}, True),

    ('a decline asked about before it is used', '''
     def g():
         made = f(1)
         if declined(made):
             return made
         return seq(made)
     ''', {}, False),

    ('declines asked about through a loop', '''
     def g():
         a = f(1)
         b = f(2)
         for one in (a, b):
             if declined(one):
                 return one
         return seq(a, b)
     ''', {}, False),

    ('a tuple asked about through the name that carries the decline', '''
     def pair():
         if f(1) is None:
             return Declined('no')
         return 1, 2
     def g():
         where, frame = pair()
         if declined(where):
             return where
         return seq(frame)
     ''', {}, False),

    ('a parser that backtracks with None', '''
     class P:
         def no(self):
             return None
         def primary(self):
             return self.no()
         def top(self):
             return seq(self.primary())
     ''', {}, False),

    ('a module function spelt like a declining method', '''
     import targets
     def unfolding(x):
         return Declined('no')
     def g(item):
         lemma, flipped = targets.unfolding(item)
         return seq(lemma)
     ''', {'targets': frozenset()}, False),
]


# A class split over two files is one object: what one file's method gives
# back is reached through `self` from the other. Each: what it is, the second
# file, and whether the stage must report it.
PART = '''
class Part:
    def route(self, x):
        if x:
            return Declined('no')
        return x
'''

SPLIT = [
    ('a decline reached through self from a class in another file', '''
     class Whole(Part):
         def g(self):
             return seq(self.route(1))
     ''', True),

    ('a method of the same name on a class that is no relative', '''
     class Other:
         def g(self):
             return seq(self.route(1))
     ''', False),
]


def main():
    passed = failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        for i, (name, body, reported) in enumerate(SPLIT):
            here = Path(tmp) / f'split{i}'
            here.mkdir()
            part, whole = here / 'part.py', here / 'whole.py'
            part.write_text(PART, encoding='utf-8')
            whole.write_text(textwrap.dedent(body), encoding='utf-8')
            seen = declines.across([str(part), str(whole)])
            found = declines.sites(str(whole), *seen[str(whole)])
            if bool(found) == reported:
                print(f'  {"caught" if reported else "silent"}        {name}')
                passed += 1
            else:
                said = f'reported {found}' if found else 'said nothing'
                print(f'  {"NOT CAUGHT" if reported else "FALSE ALARM"}  '
                      f'{name}\n      {said}')
                failed += 1
        for i, (name, body, others, reported) in enumerate(CASES):
            path = Path(tmp) / f'case{i}.py'
            path.write_text(DECLINER + textwrap.dedent(body), encoding='utf-8')
            found = declines.sites(str(path), others)
            if bool(found) == reported:
                print(f'  {"caught" if reported else "silent"}        {name}')
                passed += 1
            else:
                said = (f'reported {found}' if found
                        else 'said nothing')
                print(f'  {"NOT CAUGHT" if reported else "FALSE ALARM"}  '
                      f'{name}\n      {said}')
                failed += 1
    print(f'\n{passed} right, {failed} wrong, of {len(CASES) + len(SPLIT)} '
          f'planted cases')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
