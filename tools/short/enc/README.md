# The encoder: generator trees as Lean certificates

`Enc.lean` reads a tree from the generator (`../cert/tree2txt.py`), walks it with the checker's state of the node
(shape, constraints, box, sign) and writes a `ShortSieveCert.Cert` for `ShortSieveCert.run`, choosing the details with
the checker's own functions: the constraint behind each moved end (`Cert.up`) and each empty node (`Cert.outC`,
`Cert.outE`), the labels and the active constraints of the tests (trying none, then short ordered lists, then a
combined constraint, `Cert.comb`), the drop's bound (product or chain, with the chain's breakpoints), and the cuts of a
virtual split. A test that fails on a box is retried after cutting the box's widest coordinate. The result is checked
by `run`, in compiled Lean, before it is written.

    lake env lean --run tools/short/enc/Enc.lean TREE.txt K J R OUT.txt [tol rounds partRounds lit prune minGain]

for the cell `(K, J)` of region C (`R = 1`) or outside it (`R = 0`). `prof` and `dropbench` as the first argument write
Lean files that time each node of the certificate, or its drops, in the kernel.
