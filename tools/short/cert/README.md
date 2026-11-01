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

The root node is dropped as a last resort where no decision passes it: in the cells with `α₁` up to `1/2`, the
checker's slack admits a sliver beyond the domain (`α₁ ∈ [1/2, 1/2 + 1/DEN)`) where no test holds; the drop's bound
there is negligible, and the checker allows a drop of the shape `.std 1`.

`n2drop=1` lets the root drop wherever the generator's cost (loss plus `lambda` per node) says so, not only as a
last resort, and `altminus=0` turns off the comparison of alternative decompositions for the `−` nodes, which only
costs time. On the heaviest cells this drops the whole cell: root 125 (the cell `(17, 7)`) takes one node at loss
0.0221, against 81,680 nodes at 0.0274 without it (its Monte Carlo truth is 0.0125). On the middle of region C it
drops cells far above their truth (root 93: 0.0299 against 0.0043), and over all cells, with `lambda = 5e-8` and
`vsw = 3`, region C comes to about 2.8 times its truth: 0.523 over 127 of the 144 cells, with the cells outside
region C at 0.459 over 59 of 60, so the total is above 1.
