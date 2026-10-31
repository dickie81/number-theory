#!/bin/bash
# Build the harness: fetch R. Li's 0.521 code from arXiv (not redistributed here), derive the theta-parametric
# predicates and the Hoelder tuples from it, tabulate delta_req (about 8 minutes), and compile. With --validate, also
# check that the parametric predicates agree with Li's own at theta = 0.521 on sampled points of every loss term.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p li
if [ ! -f li/LB_521_160_1.cpp ]; then
  curl -sSL -o li/LB_521_160_1.cpp https://arxiv.org/src/2308.04458v8/anc/LB_521_160_1.cpp
fi
echo "421d18b6ff72828b170b21ae0bf03e8f300b4589b82f0cd93186932aec07af7f  li/LB_521_160_1.cpp" | sha256sum -c -
python3 -I make_li_param.py li/LB_521_160_1.cpp .
[ -f dtables.h ] || python3 gen_table.py
g++ -O3 -march=native -std=c++17 -pthread -o harness_theta harness_theta.cpp
if [ "${1:-}" = "--validate" ]; then
  g++ -O2 -std=c++17 -o val_orig val_orig.cpp
  g++ -O2 -std=c++17 -o val_param val_param.cpp
  if cmp -s <(./val_orig) <(./val_param); then echo "VALIDATE PASS: identical at theta = 0.521"; else echo "VALIDATE FAIL"; exit 1; fi
fi
