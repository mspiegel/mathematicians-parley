#!/usr/bin/env bash
# Everything that must pass before a commit, with what can run at once run
# at once.
#
# Two lanes run side by side, because cargo locks each build directory and
# the two lanes build into different ones:
#
#   debug:    cargo clippy, then cargo test          (target/debug)
#   release:  cargo build --release, then parley build, then parley gate
#                                                    (target/release)
#
# Formatting is checked first; it takes a moment and needs no build. While
# the lanes run, a line says when each step starts and how it ends, with how
# long it took. Each lane's full output is kept in a log and printed once
# both are done, lane by lane, so the report reads in order however the two
# interleaved.
#
# The tests read the built files, and parley build rewrites any that are out
# of date. If it changes one, the tests may have read the old one, so that is
# reported as a failure: rebuilt artifacts are to be committed, and the
# script run again.
#
# Usage:  scripts/precommit.sh     (from anywhere in the working tree)
# Exits non-zero when anything fails.

set -u
cd "$(git rev-parse --show-toplevel)" || exit 2

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
    ./target/release/parley build >"$logs/build.out"
    local status=$?
    cat "$logs/build.out"
    return $status
}

debug_lane() {
    step debug "cargo clippy" cargo clippy --all-targets -- -D warnings || return 1
    step debug "cargo test" cargo test || return 1
}

release_lane() {
    step release "cargo build --release" cargo build --release || return 1
    step release "parley build" parley_build || return 1
    step release "parley gate" ./target/release/parley gate || return 1
}

debug_lane >"$logs/debug.log" 2>&1 &
debug=$!
release_lane >"$logs/release.log" 2>&1 &
release=$!

failed=""
wait "$debug" || failed="$failed debug-lane"
wait "$release" || failed="$failed release-lane"

cat "$logs/debug.log"
cat "$logs/release.log"

# A build that changed files ran while the tests were reading them.
if [ -f "$logs/build.out" ] && ! grep -q " 0 changed$" "$logs/build.out"; then
    failed="$failed artifacts-changed"
    echo
    echo "parley build rewrote artifacts: commit them and run this again"
fi

echo
if [ -n "$failed" ]; then
    echo "NOT READY:$failed"
    exit 1
fi
echo "ready to commit"
