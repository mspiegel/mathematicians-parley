#!/usr/bin/env python3
"""Every file this project generates, what generates it, and where it goes.

Nothing here is new work: each artifact was already produced by running one
script and redirecting it somewhere. What was missing is a list of which
script and which somewhere, so that knowledge lived in six usage lines that a
person read and followed by hand. One of them named a path nothing reads, and
the build went on looking as though it had worked.

The order below is a real constraint and was not written down anywhere
either. `definitions.mm` has to exist before `build-geometry.py` runs, because
that script reads it for the constant it introduces; `geometry.mm` has to
exist before any theorem elaborates, because `elaborate.py` reads it so a
`target` may name one of its labels. The five hand-written proofs read nothing
and can be built at any point.

What this does not do is notice that an artifact is out of date. Nothing here
compares an artifact against its sources, and an artifact cannot be compared
against set.mm at all, since set.mm is not in the repository. Regenerating is
cheap; run it after changing the elaborator or the database.

Usage:  parley/build.py [name] [set.mm]
Exits non-zero when a recipe fails.
"""
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from library import where_set_mm

ROOT = Path(__file__).resolve().parent.parent
# Stands in the recipe where the library's path goes, which is not known
# until the command line and the environment have been asked.
SETMM = '<set.mm>'


@dataclass(frozen=True)
class Artifact:
    """One generated file: what makes it, where it goes, who reads it."""

    name: str
    path: str
    recipe: tuple
    verified: bool      # one of the files `parley/verify.py` checks


# The ten readable proofs the elaborator can expand. The file each writes is
# named for the theorem, which is not always the name of the proof file:
# `prime-above` is elaborated from `proof/infinitely-many-primes.proof` and
# `geometric-sum` from `proof/geometric-series.proof`.
THEOREMS = ('odd-square', 'even-square', 'sum-formula', 'abs-bounds',
            'triangle-inequality', 'cantor', 'isosceles', 'sqrt2-irrational',
            'prime-above', 'geometric-sum')

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
             ('elaboration/build-geometry.py', SETMM), True),
    *(Artifact(name, f'elaboration/elaborated/{name}.mm',
               ('parley/elaborate.py', name, SETMM), True)
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

    changed = 0
    for artifact in wanted:
        written = produce(artifact, library)
        if written is None:
            return 1
        where = ROOT / artifact.path
        before = where.read_text() if where.exists() else None
        where.parent.mkdir(parents=True, exist_ok=True)
        where.write_text(written)
        mark = ' ' if written == before else '*'
        print(f'{mark} {artifact.path}')
        changed += written != before

    print(f'\n{len(wanted)} built, {changed} changed')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
