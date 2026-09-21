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
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import targets
from library import read as read_library
from parse import Problem, check_encoding, parse_database

ROOT = Path(__file__).resolve().parent.parent


def where_set_mm(argv):
    """The library, said on the command line, in the environment, or here."""
    for said in (argv[1] if len(argv) > 1 else None, os.environ.get('SET_MM'),
                 ROOT / 'set.mm'):
        if said and Path(said).exists():
            return Path(said)
    return None


def named(records):
    """Every label the databases name, with where each was written.

    A `target` is reverse Polish or a list of labels, a `defines` is reverse
    Polish, and `metamath` is prose meant for a person — it names labels too
    but in a sentence, so it is not read here. An entry that is one of the
    markers `targets.MARKERS` names says how to read the lemma beside it
    rather than naming one of its own."""
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
    for one in targets.MEMBERSHIP:
        out.setdefault(one, ('parley/targets.py', 0, 'MEMBERSHIP'))
    return out


def supplied(records):
    """The labels this corpus introduces, which set.mm will not have.

    A definition that carries a `symbol` brings a constant and the axiom
    defining it; `elaboration/geometry.mm` brings whatever it proves."""
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
    for path in sorted((ROOT / 'db').glob('*.db')):
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
