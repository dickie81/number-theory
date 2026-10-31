# The encoder: generator trees as Lean certificates

`Enc.lean` reads a tree from the generator (`../cert/tree2txt.py`), walks it with the checker's state of the node
(shape, constraints, box, sign) and writes a `ShortSieveCert.Cert` for `ShortSieveCert.run`, choosing the details with
the checker's own functions: the constraint behind each moved end (`Cert.up`) and each empty node (`Cert.outC`,
`Cert.outE`), the labels and the active constraints of the tests (trying none, then short ordered lists, then a
combined constraint, `Cert.comb`), the drop's bound (product or chain, with the chain's breakpoints), and the cuts of a
virtual split. Repeated constraints are searched once. A test that fails on a box is retried after cutting the box's
widest coordinate; a Buchstab step or role reversal whose Type I test fails is retried on the halves of a cut box, its
subtree walked again for each. The result is checked by `run`, in compiled Lean, before it is written.

    lake env lean --run tools/short/enc/Enc.lean TREE.txt K J R OUT.txt [tol rounds partRounds lit prune minGain]

for the cell `(K, J)` of region C (`R = 1`) or outside it (`R = 0`). `prof` and `dropbench` as the first argument write
Lean files that time each node of the certificate, or its drops, in the kernel.

`cell` as the first argument writes the cell's certificate as one Lean file whose kernel memory stays bounded:

    lake env lean --run tools/short/enc/Enc.lean cell TREE.txt K J R OUT.lean NAME CAP tools/short/enc/CertHead.lean

The certificate is cut at the subtrees whose estimated kernel cost is at most `CAP` ms (`ownCost`); each becomes a
definition in a compact prefix form, read by the term elaborator `cert_data%` (one string per definition, so the
elaborator never sees the certificate as syntax), and the nodes above them form the top, with the subtrees as
references. The cell's theorem applies the node lemmas (`run_up_of`, `run_comb_of`, `run_split_of`, `run_cut_of`,
`run_dec_std_of`, `run_rev_std_of`) down to the cut points, and proves each cut point by `decide +kernel`, which
checks it as an auxiliary lemma of its own, with its own kernel caches. `CertHead.lean` holds the elaborator and the
node lemmas, read as the header of the files `cell` writes.

The kernel's memory grows with the reductions of one check (about 80 MB per second of kernel time), so a whole cell
cannot be one `decide +kernel`: root 53 (the cell `(8, 7)`: 27k generator nodes, 87k certificate nodes) needs more
than 9 GB that way. Cut at `CAP = 15000` it has 171 cut points and takes 731 s of kernel time, at most 21 s and
2.2 GB for a cut point.
