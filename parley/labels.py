#!/usr/bin/env python3
"""Every set.mm label this corpus names, checked against set.mm.

The database names labels from memory — a `target` field says which lemma a
word lands on, a `defines` field spells a definition's body — and nothing
else in this project notices when one of them is wrong. Every other check
here compares the corpus against itself; this is the one that compares it
against something outside.

It is a set membership and nothing more, so it costs a pass over set.mm and
no verification. `ELABORATION.md` argues for it: the check ran once from a
scratch copy and found one wrong field in 193, and what it could not do
while the file was temporary was run in the gate, so the next wrong label
would sit there as long as that one did.

set.mm is 51 MB and belongs to metamath, so it is not in this repository.
Say where it is with `SET_MM`, or leave a copy or a link at the root of the
working tree.

Usage:  parley/labels.py [set.mm]
Exits non-zero when a label is named that set.mm does not have.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import rules
import targets
from build import path_of
from library import read as read_library
from library import where_set_mm
from parse import Problem, corpus

ROOT = Path(__file__).resolve().parent.parent
# What a set.mm label looks like, strictly enough that no word of a sentence
# is mistaken for one: lower case, and hyphenated only as `df-` names are.
LABEL_SHAPED = re.compile(r'[a-z][a-z0-9]*(?:-[a-z0-9]+)*')
# What a label in a rule table looks like. A table holds nothing but labels
# and a few symbols, so this admits what prose would not: a leading digit, as
# in `1re`, and a dot, as in `pm2.21dd`.
TABLED = re.compile(r'[a-z0-9][a-z0-9.]*(?:-[a-z0-9.]+)*')


def named(records):
    """Every label the databases name, with where each was written.

    A `target` is reverse Polish or a list of labels and a `defines` is
    reverse Polish, so every token in either is a label unless it is a hole
    or one of the markers `targets.MARKERS` names, which say how to read the
    lemma beside them rather than naming one.

    `metamath` is prose meant for a person and names its labels in a
    sentence, so it is read only as far as it is certainly naming them: the
    leading entries that are a single label-shaped word, stopping at the
    first that is not. `df-dvds, whose right side is the same existential`
    gives one label and then stops; `Σ over 0...n with fsum1 and fsump1`
    gives none, and the two it hides are the price of never calling a word
    a label because it sat in a sentence.

    That field is where the check's first run found its one error — a
    `dvds` that meant `df-dvds` — so leaving it out would leave out the
    thing the check was built for.
    """
    out = {}
    for r in records:
        for field in ('target', 'defines'):
            if field not in r.fields:
                continue
            value = r.fields[field]
            # What a target writes after `with` is the lemma's variables and
            # the item's own formulas for them, which are not labels and are
            # not set.mm's words. Only the head before it names a lemma.
            if field == 'target' and ' with ' in value:
                value = value.partition(' with ')[0]
            for entry in targets.split_entries(value):
                if entry in targets.MARKERS:
                    continue
                for token in entry.split():
                    if targets.HOLE.fullmatch(token):
                        continue
                    out.setdefault(token, (r.path, r.line, r.name))
        for entry in targets.split_entries(r.fields.get('metamath', '')):
            if not LABEL_SHAPED.fullmatch(entry):
                break
            out.setdefault(entry, (r.path, r.line, r.name))
    for table, one in tabled():
        out.setdefault(one, ('parley/rules.py', 0, table))
    return out


def tabled():
    """Every label the elaborator's rule tables name, with its table.

    The tables are `parley/rules.py`'s upper-case names, and every string
    in one is a label, keys and values alike, except where it is plainly
    not one: a relation's symbol, the marker `TURNED`, or the upper-case
    name of a lemma's variable. `SYSTEMS` is read by its keys alone, since
    each value is the suffix a digit's label ends with and not a label.
    """
    def strings(value):
        if isinstance(value, str):
            yield value
        elif isinstance(value, dict):
            for key, inner in value.items():
                yield from strings(key)
                yield from strings(inner)
        elif isinstance(value, (list, tuple, set, frozenset)):
            for inner in value:
                yield from strings(inner)

    for table in sorted(n for n in vars(rules) if n.isupper()):
        value = getattr(rules, table)
        if table == 'SYSTEMS':
            value = list(value)
        for one in strings(value):
            if TABLED.fullmatch(one):
                yield table, one


def supplied(records):
    """The labels this corpus introduces, which set.mm will not have.

    A definition that carries a `symbol` brings a constant and the axiom
    defining it; `proved.mm` brings whatever it proves, and
    `parley/build.py` is what says where that file is.
    """
    out = set()
    for r in records:
        if 'symbol' in r.fields:
            token = r.fields['symbol'].strip()
            out.update({f'c{token}', f'df-{token}'})
    built = path_of('stdlib/proved')
    if built.exists():
        out.update(read_library(built))
    return out


def main(argv):
    library = where_set_mm(argv)
    if library is None:
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2
    try:
        records, theorems = corpus(ROOT)
    except Problem as trouble:
        print(trouble, file=sys.stderr)
        return 2
    # A proved theorem's `metamath` line says which set.mm theorem is its
    # counterpart, and is checked like any record's.
    wanted = named([*records, *theorems])
    have = set(read_library(library)) | supplied(records)
    missing = sorted((place, line, who, label)
                     for label, (place, line, who) in wanted.items()
                     if label not in have)
    for place, line, who, label in missing:
        print(f'{place}:{line}  {who} names {label}, '
              f'which {library.name} does not have')
    print(f'\n{len(wanted)} labels named, {len(missing)} not in '
          f'{library.name}')
    return 1 if missing else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
