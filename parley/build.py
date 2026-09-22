#!/usr/bin/env python3
"""Every file this project generates, what generates it, and where it goes.

Nothing here is new work: each artifact was already produced by running one
script and redirecting it somewhere. What was missing is a list of which
script and which somewhere, so that knowledge lived in six usage lines that a
person read and followed by hand. One of them named a path nothing reads, and
the build went on looking as though it had worked.

Which artifact has to exist before which is a real constraint, and `needs`
is where it is written. `definitions.mm` has to exist before
`build-geometry.py` runs, because that script reads it for the constant it
introduces; `geometry.mm` has to exist before any theorem elaborates, because
`elaborate.py` reads it so a `target` may name one of its labels. The five
hand-written proofs read nothing.

Saying it in a field rather than in the order of the list is what lets the
fifteen that wait for nothing run at once. They are separate processes
writing separate paths and sharing only the machine, so the only thing the
concurrency costs is memory: each holds its own copy of the library.

What this does not do is notice that an artifact is out of date. Nothing here
compares an artifact against its sources, and an artifact cannot be compared
against set.mm at all, since set.mm is not in the repository. Regenerating is
cheap; run it after changing the elaborator or the database.

Usage:  parley/build.py [name] [set.mm]
Exits non-zero when a recipe fails.
"""
import functools
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from library import where_set_mm
from parse import corpus

ROOT = Path(__file__).resolve().parent.parent
# How a proof names a theorem, wherever it names one: in the justification
# that cites it and in the justification of a `requires` line.
CITES = re.compile(r'\bthm:([A-Za-z0-9-]+)')
# Stands in the recipe where the library's path goes, which is not known
# until the command line and the environment have been asked.
SETMM = '<set.mm>'
# How many recipes run at once. Each holds its own copy of set.mm's 51,256
# signatures and peaks near 550MB, so the ceiling is there to keep a wave of
# fifteen from asking for eight gigabytes at once.
WORKERS = min(8, os.cpu_count() or 1)


@dataclass(frozen=True)
class Artifact:
    """One generated file: what makes it, where it goes, who reads it."""

    name: str
    path: str
    recipe: tuple
    verified: bool      # one of the files `parley/verify.py` checks
    needs: tuple = ()   # artifacts whose files this recipe reads


# The fifteen readable proofs the elaborator can expand. The file each
# writes is named for the theorem, which is not always the name of the proof
# file: `prime-above` is elaborated from `proof/infinitely-many-primes.proof`,
# `geometric-sum` from `proof/geometric-series.proof`, both `subsets-count`
# and `powerset-split-disjoint` from `proof/subsets.proof`, both
# `least-combination-divides` and `bezout` from `proof/bezout.proof`, and
# four from `proof/sqrt2-irrational.proof`, which holds the theorem it is
# named for and the three it leans on.
THEOREMS = ('odd-square', 'even-square', 'sum-formula', 'abs-bounds',
            'triangle-inequality', 'cantor', 'isosceles', 'lowest-terms',
            'sqrt2-irrational', 'prime-above', 'geometric-sum',
            'least-combination-divides', 'bezout', 'powerset-split-disjoint',
            'subsets-count')

# The five proofs worked out by hand, which share two of their names with
# elaborated ones and are told apart here by the prefix. `ELABORATION.md`
# compares the two of each pair.
BY_HAND = ('parity', 'sqrt2', 'algebra', 'sum-formula', 'abs-bounds')

ARTIFACTS = [
    Artifact('definitions', 'elaboration/elaborated/definitions.mm',
             ('parley/elaborate.py', '--definitions', SETMM), True),
    # Hand-written like the five below, and generated like the eleven above:
    # `build-geometry.py` holds its proofs, so it sits outside the directory
    # of things elaborated from the readable layer, and is still built here.
    Artifact('geometry', 'elaboration/geometry.mm',
             ('elaboration/build-geometry.py', SETMM), True,
             ('definitions',)),
    *(Artifact(name, f'elaboration/elaborated/{name}.mm',
               ('parley/elaborate.py', name, SETMM), True, ('geometry',))
      for name in THEOREMS),
    *(Artifact(f'hand-{name}', f'elaboration/{name}.mm',
               (f'elaboration/build-{name}.py',), False)
      for name in BY_HAND),
]


def verified():
    """The files that together are the corpus a verifier is given.

    `parley/verify.py` asks for this rather than reading a directory, because
    they do not all live in one and two of them share a basename with a file
    that is not among them."""
    return [ROOT / a.path for a in ARTIFACTS if a.verified]


def path_of(name):
    """Where one artifact goes, for a tool that reads it rather than builds
    it. `parley/labels.py` and `parley/elaborate.py` both want geometry.mm,
    and three copies of a path are three chances for two of them to agree."""
    for artifact in ARTIFACTS:
        if artifact.name == name:
            return ROOT / artifact.path
    raise KeyError(name)


def wants_library(artifact):
    return SETMM in artifact.recipe


def produce(artifact, library):
    """Run one recipe and return what it wrote, or None if it failed."""
    argv = [sys.executable] + [str(library) if part == SETMM else part
                               for part in artifact.recipe]
    done = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    if done.returncode != 0:
        print(f'{artifact.name}: {artifact.recipe[0]} failed', file=sys.stderr)
        print(done.stderr.rstrip(), file=sys.stderr)
        return None
    return done.stdout


@functools.cache
def citing():
    """For each theorem, the theorems of this corpus its proof cites.

    A proof citing another proof's theorem reads the file that theorem was
    written to, because it has to push a term for each variable of that
    statement in the order that file declares them, and two proofs need not
    spell a statement's bound names alike. So the file has to be there
    first, which is what `needs` is for.

    Which those are is already written down twice over — `proved-in` in
    `db/items.records` says a theorem is this corpus's, and the proof text
    says which it cites — so it is read and not listed. A list here would
    be the same knowledge in a third place, and the one that could quietly
    disagree with the proofs."""
    records, theorems = corpus(ROOT)
    ours = {r.name for r in records
            if r.kind == 'theorem' and 'proved-in' in r.fields}
    out = {}
    for theorem in theorems:
        named = []
        for step in theorem.steps:
            said = [step.just.text, *(just for _fact, just, _no
                                      in step.requires)]
            for name in {n for text in said for n in CITES.findall(text)}:
                if name in ours and name != theorem.name \
                        and name not in named:
                    named.append(name)
        out[theorem.name] = tuple(sorted(named))
    return out


def waves(wanted):
    """The artifacts in groups that may be built at the same time.

    An artifact waits for the files it reads and for nothing else, so the
    fifteen that read none of each other's go at once. A `needs` naming
    something not being built is not waited for: asking for one theorem
    rebuilds that theorem and not the geometry it reads, the same as asking
    for it before this ran concurrently."""
    here = {a.name for a in wanted}
    cited = citing()
    left, done, out = list(wanted), set(), []
    while left:
        ready = [a for a in left
                 if not ((set(a.needs) | set(cited.get(a.name, ()))) & here)
                 - done]
        out.append(ready)
        done |= {a.name for a in ready}
        left = [a for a in left if a not in ready]
    return out


def main(argv):
    wanted = [a for a in ARTIFACTS if a.name == argv[1]] if len(argv) > 1 \
        else ARTIFACTS
    if not wanted:
        print(f'no artifact {argv[1]!r}; there are: '
              f'{", ".join(a.name for a in ARTIFACTS)}')
        return 2
    library = where_set_mm(['', argv[2]] if len(argv) > 2 else [''])
    if library is None and any(wants_library(a) for a in wanted):
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2

    changed, said = 0, {}
    for wave in waves(wanted):
        # Each recipe is its own process writing its own path, so the only
        # thing a wave shares is the machine. A file is written as soon as
        # its wave is done, because the next wave reads it; what is said
        # about it waits, so the report is in the manifest's order and not
        # in the order the machine happened to finish.
        with ThreadPoolExecutor(max_workers=min(len(wave), WORKERS)) as pool:
            got = list(pool.map(lambda a: produce(a, library), wave))
        for artifact, written in zip(wave, got, strict=True):
            if written is None:
                continue
            where = ROOT / artifact.path
            before = where.read_text() if where.exists() else None
            where.parent.mkdir(parents=True, exist_ok=True)
            where.write_text(written)
            said[artifact.name] = (' ' if written == before else '*',
                                   artifact.path)
            changed += written != before
        if any(written is None for written in got):
            break

    for artifact in wanted:
        if artifact.name in said:
            mark, path = said[artifact.name]
            print(f'{mark} {path}')
    if len(said) != len(wanted):
        return 1

    print(f'\n{len(wanted)} built, {changed} changed')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
