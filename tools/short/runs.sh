#!/bin/bash
# The runs behind logs/runs1.txt ... runs4.txt (four threads; the seed and sample count of each run as recorded).
set -euo pipefail
cd "$(dirname "$0")"
H=./harness_theta
{ for TH in 0.520 0.519 0.518; do
    for P in C4DLoss C4DRRLoss C6DLoss2 C6DRRLoss2 C6DRRLoss3; do $H 2000000 4 $P 11 $TH | grep -v "^C total"; done
    for P in C6DLoss1 C6DRRLoss1; do $H 300000 4 $P 11 $TH | grep -v "^C total\|^theta"; done
    echo "=== done $TH"
  done; } > logs/runs1.txt
{ for TH in 0.519 0.5185; do
    for P in C4DLoss C4DRRLoss C6DLoss2 C6DRRLoss2; do $H 4000000 4 $P 23 $TH | grep -v "^C total"; done
    $H 600000 4 C6DLoss1 23 $TH | grep -v "^C total\|^theta"
    for P in C6DRRLoss1 C6DRRLoss3; do $H 300000 4 $P 23 $TH | grep -v "^C total\|^theta"; done
    echo "=== done $TH"
  done; } > logs/runs2.txt
{ for TH in 0.520 0.519 0.5185 0.518; do
    echo "theta $TH (8D terms)"
    $H 60000 4 UC05 31 $TH | grep -v "^C total\|^theta"
    $H 20000000 4 UC06 31 $TH | grep -v "^C total\|^theta"
    $H 2000000 4 UC07 31 $TH | grep -v "^C total\|^theta"
    echo "=== done8 $TH"
  done
  TH=0.5195
  for P in C4DLoss C4DRRLoss C6DLoss2 C6DRRLoss2; do $H 4000000 4 $P 31 $TH | grep -v "^C total"; done
  $H 1000000 4 C6DRRLoss3 31 $TH | grep -v "^C total\|^theta"
  $H 600000 4 C6DLoss1 31 $TH | grep -v "^C total\|^theta"
  $H 60000 4 UC05 31 $TH | grep -v "^C total\|^theta"
  $H 20000000 4 UC06 31 $TH | grep -v "^C total\|^theta"
  $H 2000000 4 UC07 31 $TH | grep -v "^C total\|^theta"
  echo "=== done $TH"; } > logs/runs3.txt
{ for TH in 0.5185 0.5182; do
    for P in C4DLoss C4DRRLoss C6DLoss2 C6DRRLoss2; do $H 4000000 4 $P 47 $TH | grep -v "^C total"; done
    $H 1000000 4 C6DRRLoss3 47 $TH | grep -v "^C total\|^theta"
    $H 600000 4 C6DLoss1 47 $TH | grep -v "^C total\|^theta"
    $H 60000 4 UC05 47 $TH | grep -v "^C total\|^theta"
    $H 20000000 4 UC06 47 $TH | grep -v "^C total\|^theta"
    $H 2000000 4 UC07 47 $TH | grep -v "^C total\|^theta"
    echo "=== done $TH"
  done; } > logs/runs4.txt
python3 summarize_full.py logs/runs*.txt
