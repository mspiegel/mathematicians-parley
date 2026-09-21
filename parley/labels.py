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
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import targets
from library import read as read_library
from parse import Problem, check_encoding, parse_database

ROOT = Path(__file__).resolve().parent.parent
# What a set.mm label looks like, strictly enough that no word of a sentence
# is mistaken for one: lower case, and hyphenated only as `df-` names are.
LABEL_SHAPED = re.compile(r'[a-z][a-z0-9]*(?:-[a-z0-9]+)*')


def where_set_mm(argv):
    """The library, said on the command line, in the environment, or here."""
    for said in (argv[1] if len(argv) > 1 else None, os.environ.get('SET_MM'),
                 ROOT / 'set.mm'):
        if said and Path(said).exists():
            return Path(said)
    return None


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
    thing the check was built for."""
    out = {}
    for r in records:
        for field in ('target', 'defines'):
            if field not in r.fields:
                continue
            for entry in targets.split_entries(r.fields[field]):
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
    for one in targets.MEMBERSHIP:
        out.setdefault(one, ('parley/targets.py', 0, 'MEMBERSHIP'))
    return out


def supplied(records):
    """The labels this corpus introduces, which set.mm will not have.

    A definition that carries a `symbol` brings a constant and the axiom
    defining it; `elaboration/auto/geometry.mm` brings whatever it proves."""
    out = set()
    for r in records:
        if 'symbol' in r.fields:
            token = r.fields['symbol'].strip()
            out.update({f'c{token}', f'df-{token}'})
    built = ROOT / 'elaboration' / 'auto' / 'geometry.mm'
    if built.exists():
        out.update(read_library(built))
    return out


def main(argv):
    library = where_set_mm(argv)
    if library is None:
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2
    records = []
    for path in sorted((ROOT / 'db').glob('*.records')):
        rel = str(path.relative_to(ROOT))
        try:
            records.extend(parse_database(
                rel, check_encoding(rel, path.read_bytes())))
        except Problem as trouble:
            print(trouble, file=sys.stderr)
            return 2
    wanted = named(records)
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
