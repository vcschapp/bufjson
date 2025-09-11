#!/usr/bin/env bash

# To install this script as a Git hook: make a copy; rename the copy to have a Git hook script name,
# e.g., `pre-push`; and copy the new renamed script into your local repo's `.git/hooks/` directory.

readonly scripts_dir=scripts

"${scripts_dir}/verify.sh"
