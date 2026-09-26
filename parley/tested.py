#!/usr/bin/env python3
"""Every library item is cited by something that elaborates.

An item's statement is written by hand and names the set.mm lemma it means.
The labels stage asks only that the lemma exists; whether the statement says
what the lemma says is found when a proof cites the item, the elaborator
applies the lemma, and the result verifies. An item nothing cites has never
been asked, and it can say anything.

So each item is cited by a proof under `proof/`, or by its test under
`tests/stdlib/`: a theorem whose one step cites it. A test takes the item's
hypotheses as its own and claims the item's conclusion, or for a
definition the right side of it from the left. One direction is enough: the
lemma applied either way has the whole statement to match.

An item marked `open` has no lemma to be asked against, and is not asked.
Nor is a definition that only introduces a symbol, as `angle` does: it has
no `then` line for a step to claim, and what it says, the `defines` field,
is written into `stdlib/definitions.mm`, which the verifier reads.

Usage:  parley/tested.py [root]
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from parse import cited_items, corpus, qualified


def untested(root):
    records, theorems = corpus(root)
    cited = {full for thm in theorems for full, _line in cited_items(thm)}
    return [qualified(r) for r in records
            if r.kind in ('definition', 'theorem') and 'open' not in r.fields
            and r.conclusions and qualified(r) not in cited]


def main(argv):
    root = Path(argv[1]) if len(argv) > 1 \
        else Path(__file__).resolve().parent.parent
    missing = untested(root)
    for name in missing:
        print(f'{name} is cited by no proof and has no test in tests/stdlib/')
    if missing:
        return 1
    print('every library item is cited by a proof or a test')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
