#!/usr/bin/env bash
# Print, one per line, the Lake targets that the recipe lines of the given make goals build for
# the current CHECK_TARGETS (`make check-prebuild` builds them).
#   scripts/check-build-targets.sh GOAL...
# `make -n` prints those lines with LAKE=: and PYTHON=:. It still runs the lines that name
# $(MAKE), with this script as their shell, which runs a line only if all it does is recurse.
set -euo pipefail

if [ "${1:-}" = -c ]; then
  word='[^][:space:];&|<>()`$\\]+'
  only_recursion="^(: ($word ?)*&& )*([^ ]*/)?g?make( $word)*$"
  if [[ $2 =~ $only_recursion ]]; then exec /bin/sh -c "$2"; fi
  echo "check-build-targets: make -n would run more than a recursive make: $2" >&2
  exit 1
fi

cd "$(dirname "$0")/.."
plan=$(make -n --no-print-directory SHELL="$PWD/scripts/check-build-targets.sh" LAKE=: PYTHON=: "$@")
printf '%s\n' "$plan" | sed -e ':a' -e '/\\$/N' -e 's/\\\n//' -e 'ta' |
  { grep -oE '(^|[[:space:]]): build( [^&;|<>()]*)?' || true; } |
  while read -r _ _ args; do
    case " $args " in
      *' --wfail '*) ;;
      *) echo "check-build-targets: a Lake build without --wfail: $args" >&2; exit 1 ;;
    esac
    for target in $args; do
      case $target in
        --wfail) ;;
        -*) echo "check-build-targets: unexpected Lake flag $target in: $args" >&2; exit 1 ;;
        *) echo "$target" ;;
      esac
    done
  done | sort -u
