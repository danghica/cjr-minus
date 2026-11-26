#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lake build Cjr cjr test-printer test-linked-list test-iterator test-mergesort test-mergesort-cost estimate-mergesort
lake env lean Audit.lean
lake exe test-printer
lake exe test-linked-list
lake exe test-iterator
lake exe test-mergesort
lake exe test-mergesort-cost
sh voting/check.sh
