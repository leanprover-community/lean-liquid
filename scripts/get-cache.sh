#!/usr/bin/env bash

set -o errexit      # Exit on most errors (see the manual)
set -o nounset      # Disallow expansion of unset variables
set -o pipefail     # Use last non-zero exit code in a pipeline

if ! git rev-parse HEAD > /dev/null 2>&1; then
  echo "Run this script from inside the git repository."
  exit 1
fi

cd $(git rev-parse --show-toplevel)
leanproject get-mathlib-cache

echo "Trying to download project cache"
if wget https://oleanstorage.azureedge.net/mathlib/lean-liquid/"$(git rev-parse HEAD)".tar.xz 2> /dev/null; then
  echo "Found oleans at https://oleanstorage.azureedge.net/mathlib/lean-liquid/"
  tar -xf "$(git rev-parse HEAD)".tar.xz
  rm "$(git rev-parse HEAD)".tar.xz
  echo "Extracted oleans into src and deleted archive"
else
  echo "No olean cache available"
fi
