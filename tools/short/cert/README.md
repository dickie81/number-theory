# The certificate generator (prototype)

`cert4` builds, for each root cell of region C (and the cells outside it), a tree of decisions over boxes of the
primes' exponents: empty regions, splits along a coordinate or a witness face, the Type II and Lemma 4.1 tests,
Buchstab's steps and Li's role reversals, and drops bounded by the chain bound over virtual splits. Its verifier
replays the tree with the exact checks only and sums the dropped bounds (units `2^{-50}`).

    g++ -O2 -march=native -std=c++17 -pthread -DGRID=40 -o cert4_40 cert4.cpp wit.cpp nodes.cpp
    ROOTLOG=roots.txt ./cert4_40 r0=0 r1=144 lambda=5e-8 threads=4 tree=trees/t

`-DGRID=40` is θ = 21/40 (the default), `-DGRID=50` Li's 13/25. `tree=PREFIX` writes each root's tree to
`PREFIX_<root>.bin`; `tree2txt.py` turns one into the text the encoder reads. The roots are numbered as in `roots()`:
`0 … 143` region C's cells `(k, j)`, `k = 2 + i/8`, `j = 2 + i mod 8`; `180 … 239` the cells outside region C.

The generator's domain carries the checker's slack (`2 x_k ≤ S_k + E`, `E = 1`), and its thresholds and witness faces
are Li's tightened by `MRG = 8` units of `1/DEN`, so that its decisions pass in the Lean checker, whose forms carry the
slack `H` and whose domain-aware extremes round (`exact.h`). `mc.cpp` is the Monte Carlo of the trees' true losses.
