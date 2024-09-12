#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download stdlib

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/stdlib"
  dune build --root . --only-packages=coq-stdlib @install
  dune install --root . coq-stdlib --prefix="$CI_INSTALL_DIR"
)
