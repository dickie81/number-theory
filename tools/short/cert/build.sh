#!/bin/bash
# Build the generator at theta = 21/40 (GRID=40) and the Monte Carlo of the trees' true losses.
cd "$(dirname "$0")"
g++ -O2 -march=native -std=c++17 -pthread -DGRID=${GRID:-40} -o cert4_${GRID:-40} cert4.cpp wit.cpp nodes.cpp
g++ -O2 -march=native -std=c++17 -pthread -DGRID=${GRID:-40} -o mc_${GRID:-40} mc.cpp wit.cpp nodes.cpp
