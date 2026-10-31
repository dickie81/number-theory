# Primes in short intervals at `θ = 13/25`, after R. Li: work in progress

R. Li proves that `(x − x^θ, x]` contains primes for `θ = 0.52` and large `x` (arXiv:2308.04458v8), by Harman's
sieve with Baker, Harman and Pintz's decomposition. The library is formalising that proof, with Hölder's inequality
with real exponents and Huxley's large values in place of Li's Type II lemmas. The formalisation is not finished: the
results below are its parts so far, and no paper of the repository claims them.

## The assembly

**Lean:** `lib/pnt/ShortSieveThree.lean`:

```lean
theorem ShortSieveThree.primes_of_cells {ρ : ℝ} (hLi : LiLemma31 (13 / 25) (2 / 25) ρ) (hρ : 0 < ρ)
    (hρθ : 12 * ρ < 1 / 25) (L : Bool → ℕ × ℕ → ℝ)
    (h : ∀ r, ∀ c ∈ cells r, OK (13 / 25) ρ 1 (fun x y => ((cell c.1 c.2 r).count x y : ℝ)) (L r c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ (13 / 25 : ℝ) ≤ y → y ≤ x ^ (1 - ρ) →
      (1 - (∑ c ∈ cells true, L true c + ∑ c ∈ cells false, L false c) - ε) * y / Real.log x ≤
        ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card
```

In words: Li's identity `S(A, √x) = S(A, x^{ν(0)}) − Σ_p S(A_p, x^{ν(α_p)}) + Σ₃` holds exactly in any interval
(`ShortSieveTop.top_identity`). Its first two sums are asymptotic by Li's Lemma 3.1 (`ShortSieveRoot.abs_S1_sub_le`,
`ShortSieveRoot.abs_S2_liNu_sub_le`), and the terms of `Σ₃` are the counts of the certificate's root cells, the cells
`(k/50, (k + 1)/50] × [j/50, (j + 1)/50)` of `(α₁, α₂)`: 253 in Li's region `C` and 91 outside it
(`ShortSieveThree.bigThree_eq_cells`). So loss bounds `L` on the cells, in the sense of `ShortSieveTree.OK`, give
`π(x) − π(x − y) ≥ (1 − ΣL − ε) y/log x` for `x^{13/25} ≤ y ≤ x^{1−ρ}`. The certificate is to supply the bounds,
with `ΣL < 1`.

## The root cells

Each root cell is a standard node with two primes (`ShortSieveCert.cell_eq_std`), and the certificate starts it with the box
`[k DEN/50, (k + 1) DEN/50 + 1) × [j DEN/50, (j + 1) DEN/50)` of the primes' coordinates and the constraints `q < p`,
`q ≤ ρ`, Li's level and the region: `ShortSieveCert.Sound.cell`. The cell's conditions keep the invariants of the
standard nodes: `ShortSieveCert.StdInv.cell`, `ShortSieveCert.CondsOK.cell`.

## The certificate's decisions

A cell's bound comes from a tree of decisions on nodes of Li's decomposition (`ShortSieveNode.Node`: primes and
rough items with log-linear conditions). Each decision is a theorem:

- an empty region has no loss: `ShortSieveCert.Sound.OK_of_out`;
- a split by a condition and its negation adds the two losses (`ShortSieveTree.count_split`,
  `ShortSieveCert.OK_of_split`), keeps the certificate's coordinates (`ShortSieveCert.Sound.cut_lt`,
  `ShortSieveCert.Sound.cut_ge` for a box cut) and, for a standard node, its invariants
  (`ShortSieveCert.StdInv.cons`, `ShortSieveCert.CondsOK.split`);
- a box passing the Type II test with real exponents is asymptotic: `ShortSieveCert.Sound.asym_of_tii`, from Harman's
  test on a compact set (`ShortSieveNode.abs_count_sub_le_of_test`) and the moment lemma
  (`ShortSieveGroup.moment_group_from`);
- a box with two grouped variables in Li's Lemma 4.1's region is asymptotic: `ShortSieveCert.Sound.asym_of_g2`, from
  `ShortSieveLi.abs_count_sub_le_G2_eps`;
- a dropped box is bounded in the comparison interval: `ShortSieveDrop.count_le_drop1`, `ShortSieveDrop.count_le_drop2`;
  for a standard node (primes and one rough item, sifted by the last prime), by `ω*` and Mertens' sums over the box:
  `ShortSieveCert.Sound.OK_of_drop`, with `ω*` bounded on the box's range by Buchstab's `ω`
  (`ShortSieveCert.omegaC_le_omUpK`);
- Buchstab's identity and Li's role reversals are exact identities between counts: `ShortSieveBuch.count_buchstab`,
  `ShortSieveBuch.count_rev`, with the certificate's coordinates kept by `ShortSieveCert.Sound.buch`; the Type I terms
  they leave are asymptotic by Li's Lemmas 3.1 and 3.2 (`ShortSieveTypeI.abs_count_sub_le_typeI`). For a standard node,
  Buchstab's step at the level `x^{1/25}` with the box in Li's regions `D′₀`, `D′₁` or `D′₂` leaves the node the child's
  loss: `ShortSieveCert.Sound.OK_of_dec`; the child keeps the coordinates and the invariants:
  `ShortSieveCert.Sound.std_child`, `ShortSieveCert.StdInv.child`, `ShortSieveCert.CondsOK.child`. Li's role reversal
  of a standard node, its first prime the Type I term's cofactor, likewise leaves the node the reversed child's loss:
  `ShortSieveCert.Sound.OK_of_rev`, with `ShortSieveCert.Sound.rev_child`, `ShortSieveCert.StdInv.rev` and
  `ShortSieveCert.CondsOK.rev` for the child.
- The reversed nodes have two rough items, and the certificate decomposes either one. Buchstab's step on the last
  rough item of any node, its box in Li's Type I regions, leaves the node the child's loss:
  `ShortSieveCert.Sound.OK_of_decL`. The child keeps the coordinates (`ShortSieveCert.Sound.last_child`), the item
  forms (`ShortSieveCert.itemsOK_last`) and the invariants (`ShortSieveCert.Inv.last`, `ShortSieveCert.CondsOK.last`).
  The invariant `ShortSieveCert.Inv` covers the standard and the reversed nodes (`ShortSieveCert.StdInv.inv`,
  `ShortSieveCert.RevInv.inv`) and survives splits (`ShortSieveCert.Inv.cons`); the reversed node's item forms are
  `ShortSieveCert.itemsOK_rev`. Swapping the two items keeps the count, the coordinates, the invariants and the
  item forms (`ShortSieveCert.count_swap`, `ShortSieveCert.Sound.swap`, `ShortSieveCert.Inv.swap`,
  `ShortSieveCert.CondsOK.swap`, `ShortSieveCert.itemsOK_swap`), so the first item can be decomposed as the last. A
  dropped node with two rough items, the second's product with some of the primes being the coordinate `0`, is
  bounded by `ω*` for each item and Mertens' sums over the box: `ShortSieveCert.Sound.OK_of_drop2`.

## How the Lean statements differ from Li's

- Li's Lemmas 3.1, 3.2 and 4.1 (Baker, Harman and Pintz's Lemmas 12, 13 and 9) are hypotheses: `LiLemma31`,
  `LiLemma32`, `LiLemma41` (`lib/pnt/ShortSieveLi.lean`). They rest on Watt's mean value theorem, which is not in the
  library.
- Li's Type II lemmas are replaced by Harman's moment lemma with real exponents, for groups of prime boxes
  (`ShortSieveGroup.moment_group_from`), proved from the library's zero-free half-plane `Re s > 11/12` with Huxley's
  large values.
- Li's `α*` is replaced by `1/2` in his Type I regions, as his code does.

These theorems are printed in `lib/check/CheckAll.lean`.

## Source

- R. Li, *On the difference between consecutive primes*, arXiv:2308.04458v8: Lemmas 3.1, 3.2, 4.1, the decomposition
  of his Section 5, and the regions `A`, `B`, `C` with the bound (12) for region `A`.
- R. C. Baker, G. Harman and J. Pintz, *The difference between consecutive primes, II*, Proc. London Math. Soc. 83
  (2001), 532–562.
- G. Harman, *Prime-Detecting Sieves*, Princeton University Press (2007).
