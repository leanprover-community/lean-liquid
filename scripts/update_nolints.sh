#!/usr/bin/env bash

set -e
set -x

# Exit if there are no changes relative to master
git diff-index --quiet refs/remotes/origin/master -- scripts/nolints.txt && exit 0

git checkout master
git add scripts/nolints.txt
git commit -m "chore(scripts): update nolints.txt"
git pull origin master || exit 0
git push origin master
