#!/usr/bin/env python3
"""Every file this project generates, what generates it, and where it goes.

Nothing here is new work: each artifact was already produced by running one
script and redirecting it somewhere. What was missing is a list of which
script and which somewhere, so that knowledge lived in six usage lines that a
person read and followed by hand. One of them named a path nothing reads, and
the build went on looking as though it had worked.

What there is to build is read off the tree rather than listed. Every theorem
of a `.proof` file is elaborated; the standard library's definitions are
written by the elaborator; and every `build-<name>.py` under `elaboration/`
writes `<name>.mm` beside it. A file's path under `elaboration/` is its name
with `.mm`, so the theorem `proof/bezout/bezout` is written to
`elaboration/proof/bezout/bezout.mm`, and a file including it says so.

Which artifact has to exist before which is a real constraint, and `needs`
is where it is written. `stdlib/definitions.mm` has to exist before a
library script such as `build-proved.py` runs, because that script reads it
for the constant it introduces; every library file has to exist before any
theorem elaborates, because `elaborate.py` reads them so a `target` may name
one of their labels; and a theorem waits for the theorems it cites. The
hand-written proofs beside `elaboration/` itself read nothing.

Saying it in a field rather than in the order of the list is what lets the
ones that wait for nothing run at once. They are separate processes
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
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from library import where_set_mm
from parse import STDLIB, Problem, cited_items, corpus, in_stdlib, qualified

ROOT = Path(__file__).resolve().parent.parent
ELABORATION = ROOT / 'elaboration'
# The library's definitions, which the elaborator writes and everything reads.
DEFINITIONS = f'{STDLIB}/definitions'
# Stands in the recipe where the library's path goes, which is not known
# until the command line and the environment have been asked.
SETMM = '<set.mm>'
# How many recipes run at once. Each holds its own copy of set.mm's 51,256
# signatures and most peak near 550MB, so the ceiling is there to keep a wave
# of every theorem at once from asking for gigabytes the machine may not have.
WORKERS = min(8, os.cpu_count() or 1)
# What one recipe may use at its peak before the build fails. A proof is
# built as steps that share their parts (`spell.Step`), and no recipe peaks
# above 0.6GB; built as text, with every shared part written out again, the
# intermediate value theorem took 6GB. The limit is well above what any
# recipe needs and well below that, so a recipe that grows past it is
# reported rather than left to the machine.
MEMORY_LIMIT = 2 << 30
# `ru_maxrss` is in bytes on macOS and in kilobytes elsewhere.
RSS_UNIT = 1 if sys.platform == 'darwin' else 1024


@dataclass(frozen=True)
class Artifact:
    """One generated file: what makes it, where it goes, who reads it."""

    name: str           # its path under elaboration/, without `.mm`
    recipe: tuple
    verified: bool      # one of the files `parley/verify.py` checks
    needs: tuple = ()   # artifacts whose files this recipe reads

    @property
    def path(self):
        return str(path_of(self.name).relative_to(ROOT))


def path_of(name):
    """Where one artifact goes, for a tool that reads it rather than builds
    it. The name is the path, so this is the one place that says how.
    """
    return ELABORATION / f'{name}.mm'


def scripts(where):
    """The hand-written builders in one directory, by what each builds."""
    return {script.stem[len('build-'):]: script
            for script in sorted(where.glob('build-*.py'))}


@functools.cache
def artifacts():
    """Every file this project generates, read off the working tree.

    In the order they are reported: the library's files, the theorems in
    the order their proof files are read, and the hand-written proofs that
    `ELABORATION.md` compares with the elaborated ones.
    """
    _records, theorems = corpus(ROOT)
    library = [Artifact(DEFINITIONS,
                        ('parley/elaborate.py', '--definitions', SETMM), True)]
    for stem, script in scripts(ELABORATION / STDLIB).items():
        library.append(Artifact(f'{STDLIB}/{stem}',
                                (str(script.relative_to(ROOT)), SETMM), True,
                                (DEFINITIONS,)))
    reads = tuple(a.name for a in library)
    ours = {qualified(thm) for thm in theorems}
    proved = []
    for thm in theorems:
        name = qualified(thm)
        # A proof citing another proof's theorem reads the file that theorem
        # was written to, because it has to push a term for each variable of
        # that statement in the order that file declares them, and two
        # proofs need not spell a statement's bound names alike. So that
        # file has to be there first. Which theorems those are is read off
        # the citations, the same way the checker reads them.
        cited = dict.fromkeys(full for full, _line in cited_items(thm)
                              if full in ours and full != name
                              and not in_stdlib(full))
        proved.append(Artifact(name, ('parley/elaborate.py', name, SETMM),
                               True, (*reads, *cited)))
    by_hand = [Artifact(stem, (str(script.relative_to(ROOT)),), False)
               for stem, script in scripts(ELABORATION).items()]
    return (*library, *proved, *by_hand)


def verified():
    """The files that together are the corpus a verifier is given.

    `parley/verify.py` asks for this rather than reading a directory, because
    the hand-written comparisons sit beside them and are not among them.
    """
    return [ROOT / a.path for a in artifacts() if a.verified]


def wants_library(artifact):
    return SETMM in artifact.recipe


@dataclass(frozen=True)
class Made:
    """What one recipe wrote, None where it failed, and its peak memory."""

    written: str
    peak: int


def produce(artifact, library):
    """Run one recipe, and say what it wrote and how much memory it took.

    The child is reaped with `os.wait4`, which reports that one process's
    peak; `subprocess.run` reaps it without saying, and the whole build's
    figure cannot tell one recipe from the seven beside it. Its two streams
    are read at once, since a child filling one while the other is waited
    on would never finish.
    """
    argv = [sys.executable] + [str(library) if part == SETMM else part
                               for part in artifact.recipe]
    child = subprocess.Popen(argv, cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
    with ThreadPoolExecutor(max_workers=2) as streams:
        out = streams.submit(child.stdout.read)
        err = streams.submit(child.stderr.read)
        written, complained = out.result(), err.result()
    _pid, status, usage = os.wait4(child.pid, 0)
    child.returncode = os.waitstatus_to_exitcode(status)
    peak = usage.ru_maxrss * RSS_UNIT
    if child.returncode != 0:
        print(f'{artifact.name}: {artifact.recipe[0]} failed', file=sys.stderr)
        print(complained.rstrip(), file=sys.stderr)
        return Made(None, peak)
    return Made(written, peak)


def waves(wanted):
    """The artifacts in groups that may be built at the same time.

    An artifact waits for the files it reads and for nothing else, so the
    ones that read none of each other's go at once. A `needs` naming
    something not being built is not waited for: asking for one theorem
    rebuilds that theorem and not the geometry it reads, the same as asking
    for it before this ran concurrently.
    """
    here = {a.name for a in wanted}
    left, done, out = list(wanted), set(), []
    while left:
        ready = [a for a in left if not (set(a.needs) & here) - done]
        out.append(ready)
        done |= {a.name for a in ready}
        left = [a for a in left if a not in ready]
    return out


def main(argv):
    try:
        every = artifacts()
    except Problem as trouble:
        print(trouble, file=sys.stderr)
        return 2
    wanted = [a for a in every if a.name == argv[1]] if len(argv) > 1 \
        else list(every)
    if not wanted:
        print(f'no artifact {argv[1]!r}; there are: '
              f'{", ".join(a.name for a in every)}')
        return 2
    library = where_set_mm(['', argv[2]] if len(argv) > 2 else [''])
    if library is None and any(wants_library(a) for a in wanted):
        print('set.mm not found; say where it is with SET_MM, or leave a '
              'copy or a link at the root of the working tree')
        return 2

    changed, said, peaks = 0, {}, {}
    for wave in waves(wanted):
        # Each recipe is its own process writing its own path, so the only
        # thing a wave shares is the machine. A file is written as soon as
        # its wave is done, because the next wave reads it; what is said
        # about it waits, so the report is in the manifest's order and not
        # in the order the machine happened to finish.
        with ThreadPoolExecutor(max_workers=min(len(wave), WORKERS)) as pool:
            made = list(pool.map(lambda a: produce(a, library), wave))
        got = [one.written for one in made]
        for artifact, one in zip(wave, made, strict=True):
            peaks[artifact.name] = one.peak
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

    # What the largest recipe took, always, and every recipe past the
    # limit, which fails the build: the files are written, and what they
    # cost is the defect.
    heaviest = max(peaks, key=peaks.get)
    print(f'\nlargest peak: {heaviest}, {peaks[heaviest] / (1 << 30):.1f}GB')
    over = [name for name, peak in peaks.items() if peak > MEMORY_LIMIT]
    for name in over:
        print(f'{name} peaked at {peaks[name] / (1 << 30):.1f}GB, past the '
              f'limit of {MEMORY_LIMIT / (1 << 30):.0f}GB', file=sys.stderr)
    if over:
        return 1

    print(f'\n{len(wanted)} built, {changed} changed')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
