#!/usr/bin/env bash

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if "$script_dir/verify.sh"; then
  git push
else
  printf "failed verify, push aborted\n" >&2
  exit 1
fi
