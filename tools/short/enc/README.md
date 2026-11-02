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

`skel` as the first argument writes the cell's certificate as a skeleton for the library's `cert_cell` command
(`lib/pnt/ShortSieveCertData.lean`):

    lake env lean --run tools/short/enc/Enc.lean skel TREE.txt K J R OUT.txt [CAP]

The kernel's memory grows with the reductions of one check (about 80 MB per second of kernel time), so a whole cell
cannot be one `decide +kernel`: root 53 (the cell `(8, 7)`: 27k generator nodes, 87k certificate nodes) needs more
than 9 GB that way. So the certificate is cut at the subtrees whose estimated kernel cost is at most `CAP` ms
(`ownCost`, default 15000), and at the leaves above them: these are the cut points, each checked by `decide +kernel`
as an auxiliary lemma of its own, with its own kernel caches, and the nodes above them form the top, which the node
lemmas of `lib/pnt/ShortSieveCertSplit.lean` (`run_up_of`, `run_comb_of`, `run_split_of`, `run_cut_of`,
`run_dec_std_of`, `run_dec_two_of`, `run_rev_std_of`, `run_swap_of`) check from the cut points' results. The skeleton
is the certificate in a prefix form with `[` before each cut point, after a header with the cell's loss and the cut
points' losses. It leaves out what the checker's state determines, which `cert_cell` recomputes as it replays the
state: the new end of a range that `Cert.up` moves, and the breakpoints of a chain drop. Compressed, it takes about
5 bytes per generator node.

`cells.py` turns skeletons into the library's cell modules and assembles them:

    python3 tools/short/enc/cells.py write ROOT SKELETON SOURCE   # lib/pnt/ShortSieve525Ckkjj.lean (or Okkjj)
    python3 tools/short/enc/cells.py assemble                     # lib/pnt/ShortSieve525.lean
    python3 tools/short/enc/cells.py check                        # registry, modules and assembly agree
    python3 tools/short/enc/cells.py rewrite                      # every module again from its own skeleton

Each cell module holds `cert_cell` on its skeleton, compressed (raw DEFLATE) and in base64, and so the cell's theorem
`Ckkjj_run`; `write` keeps a cell's module unless the new certificate's loss is smaller (or `--force`), and the
registry `cells525.tsv` records each cell's loss, cut points, size and source (the generator's options). The assembly
applies `ShortSieveCert.primes_of_certs` to the 204 cells, with the total of their losses. Cut at `CAP = 15000`,
root 53 has 171 cut points and takes 731 s of kernel time, at most 21 s and 2.2 GB for a cut point; root 125 (82k
generator nodes, 275k certificate nodes) has 608 and takes 2,490 s, at most 30.5 s and 3.1 GB for one.
