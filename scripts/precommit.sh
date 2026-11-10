#!/usr/bin/env bash
# What must pass before a commit, with what can run at once run at once.
#
# Two levels:
#
#   scripts/precommit.sh            everything: what must pass before main
#                                   receives a merge.
#   scripts/precommit.sh --branch   what must pass before a commit to a
#                                   branch: the same with the gate and the
#                                   slowest tests left out.
#
# Three lanes run one after another, each with the whole of one budget of
# threads, PRECOMMIT_THREADS (8 where it is not set):
#
#   debug:    cargo clippy                           (target/debug)
#   release:  cargo build --release, then parley build metamath and
#             parley build lean, then parley gate
#             (parley check in its place with --branch)
#   test:     cargo nextest run --release            (target/release)
#
# Every step is held to the budget: cargo compiles with that many jobs, and
# parley runs on that many threads. Lanes side by side would each take the
# whole of it. In the test lane nextest runs that many tests side by side,
# each on one thread (PARLEY_THREADS=1), so that the two do not multiply;
# a test that shares its cases out itself runs on as many threads as
# nextest gives it slots (`threads::in_order_slots`, `.config/nextest.toml`).
#
# With --branch the gate gives way to `parley check`, and the test lane
# leaves out invariance's sweep, planted_elaborate, planted_gate, coverage
# and build_failures.
# What the branch level still holds is formatting, lints, every artifact
# built and kernel-checked as it is built (and committed, below), the
# checker over the corpus, and the remaining tests, the planted checks among
# them. What it does not hold is the gate's fresh rebuild compared with the
# tree, its label, testing and requires-line stages, the respellings of
# every proof, and the planted defects of the elaborator and the gate. The
# full level runs all of them, so a branch is run at it before it is merged.
#
# The tests elaborate proofs and load set.mm, and run several times faster
# built with optimisations. nextest runs the tests of every binary in one
# pool, where cargo test runs the binaries one after another; each binary
# that reads set.mm holds one test, so set.mm is read no more often than with
# cargo test. It is installed with `cargo install cargo-nextest --locked`.
# nextest does not run doc tests, and the crate has none. The release and
# test lanes share a build directory, so the tests use the library the
# release lane compiled. The release profile keeps overflow checks for the
# tests.
#
# Formatting is checked first; it takes a moment and needs no build. A line
# says when each step starts and how it ends, with how long it took. Each
# lane's full output is kept in a log and printed once every lane is done.
#
# The tests read the built files, and parley build rewrites any that are out
# of date. A file it changes is one the commit would leave out, so that is
# reported as a failure: rebuilt artifacts are to be committed, and the
# script run again.
#
# Usage:  scripts/precommit.sh [--branch]   (from anywhere in the working tree)
# Exits non-zero when anything fails.

set -u
cd "$(git rev-parse --show-toplevel)" || exit 2

branch=""
case "${1:-}" in
    "") ;;
    --branch) branch=yes ;;
    *)
        echo "usage: scripts/precommit.sh [--branch]" >&2
        exit 2
        ;;
esac

# The tests the branch level leaves out, the slowest: invariance's sweep of
# every change at every line (its sampled mixes, at the fixed seed, stay),
# four binaries, and the test that checks every planted case twice,
# against the clean corpus read once and read afresh.
slow='(binary(invariance) & not test(in_any_mix_of_spellings)) | binary(planted_elaborate) | binary(planted_gate) | binary(coverage) | binary(build_failures) | test(=a_clean_reading_kept_reports_what_a_fresh_one_does)'

threads=${PRECOMMIT_THREADS:-8}
export CARGO_BUILD_JOBS=$threads

logs=$(mktemp -d)
trap 'rm -rf "$logs"' EXIT

# Progress goes to the terminal as it happens, through descriptor 3, while
# each lane's own output goes to its log.
exec 3>&1

# Run one step of a lane: say on the terminal that it started and how it
# ended, with how long it took, and put what it prints in the lane's log.
step() {
    local lane=$1 name=$2
    shift 2
    echo "[$lane] $name ..." >&3
    echo "=== $name"
    local began=$SECONDS
    if "$@"; then
        echo "[$lane] $name ok ($((SECONDS - began))s)" >&3
    else
        echo "[$lane] $name FAILED ($((SECONDS - began))s)" >&3
        return 1
    fi
}

echo "[start] cargo fmt --check ..."
if ! cargo fmt --check; then
    echo "NOT READY: formatting (run cargo fmt)"
    exit 1
fi
echo "[start] cargo fmt --check ok"

# The build's report is kept apart as well, to see whether it changed files.
parley_build() {
    PARLEY_THREADS=$threads ./target/release/parley build metamath >"$logs/build.out"
    local status=$?
    cat "$logs/build.out"
    return $status
}

# The Lean build only writes files, and needs no Lean installed.
parley_build_lean() {
    PARLEY_THREADS=$threads ./target/release/parley build lean >"$logs/build-lean.out"
    local status=$?
    tail -n 3 "$logs/build-lean.out"
    return $status
}

debug_lane() {
    step debug "cargo clippy" cargo clippy --all-targets -- -D warnings || return 1
}

release_lane() {
    step release "cargo build --release" cargo build --release || return 1
    step release "parley build metamath" parley_build || return 1
    step release "parley build lean" parley_build_lean || return 1
    if [ -n "$branch" ]; then
        step release "parley check" \
            env PARLEY_THREADS="$threads" ./target/release/parley check || return 1
    else
        step release "parley gate" \
            env PARLEY_THREADS="$threads" ./target/release/parley gate || return 1
    fi
}

# nextest runs $threads tests at once, each on one thread.
run_tests() {
    PARLEY_THREADS=1 cargo nextest run --release \
        --build-jobs "$threads" --test-threads "$threads" "$@"
}

test_lane() {
    if [ -n "$branch" ]; then
        step test "cargo nextest run --release (all but the slowest)" \
            run_tests -E "not ($slow)" || return 1
    else
        step test "cargo nextest run --release" run_tests || return 1
    fi
}

failed=""
debug_lane >"$logs/debug.log" 2>&1 || failed="$failed debug-lane"
release_lane >"$logs/release.log" 2>&1 || failed="$failed release-lane"
test_lane >"$logs/test.log" 2>&1 || failed="$failed test-lane"

cat "$logs/debug.log"
cat "$logs/release.log"
cat "$logs/test.log"

# A build that changed files ran while the tests were reading them.
if [ -f "$logs/build.out" ] && ! grep -q " 0 changed$" "$logs/build.out"; then
    failed="$failed artifacts-changed"
    echo
    echo "parley build rewrote artifacts: commit them and run this again"
fi
if [ -f "$logs/build-lean.out" ] && ! grep -q " 0 changed," "$logs/build-lean.out"; then
    failed="$failed lean-files-changed"
    echo
    echo "parley build lean rewrote Lean files: commit them and run this again"
fi

echo
if [ -n "$failed" ]; then
    echo "NOT READY:$failed"
    exit 1
fi
if [ -n "$branch" ]; then
    echo "ready to commit to a branch; run scripts/precommit.sh before merging to main"
else
    echo "ready to commit"
fi
