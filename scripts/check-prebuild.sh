#!/usr/bin/env bash
# Build, in one Lake process, every target that the recipe lines of the named make goals build
# (`make check-prebuild`, before `make check` overlaps its check groups). `make -n` prints each
# line the goals would run, with LAKE and PYTHON replaced by `:`, a no-op that marks the Lake
# commands. It runs only the lines that name $(MAKE); in the check groups those only recurse.
#   scripts/check-prebuild.sh GOAL...     (LAKE and CHECK_TARGETS as make passes them down)
set -euo pipefail
cd "$(dirname "$0")/.."
LAKE=${LAKE:-lake}
plan=$(make -n --no-print-directory LAKE=: PYTHON=: "$@")
# Join continued lines, keep each `: build` command up to its first shell operator, drop flags.
targets=$(printf '%s\n' "$plan" | sed -e ':a' -e '/\\$/N' -e 's/\\\n//' -e 'ta' |
  { grep -oE '(^|[[:space:](]): build [^&;|<>()]*' || true; } | sed -E 's/^.*: build //' |
  tr -s ' \t' '\n\n' | { grep -v -e '^-' -e '^$' || true; } | sort -u)
if [ -z "$targets" ]; then
  echo "check-prebuild: the selected checks build no Lake targets"
  exit 0
fi
# shellcheck disable=SC2086 # one word per target
set -- $targets
echo "check-prebuild: $# targets"
echo "$LAKE build --wfail $*"
"$LAKE" build --wfail "$@"
