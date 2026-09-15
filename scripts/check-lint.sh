#!/usr/bin/env bash
# Deprecated path, kept for compatibility: gates 1 and 2 moved to check-gates.sh.
exec "$(dirname "$0")/check-gates.sh" --gates 1,2 "$@"
