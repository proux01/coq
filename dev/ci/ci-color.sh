#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download color

ulimit -s
ulimit -s 65536
ulimit -s
( cd "${CI_BUILD_DIR}/color" && make )
