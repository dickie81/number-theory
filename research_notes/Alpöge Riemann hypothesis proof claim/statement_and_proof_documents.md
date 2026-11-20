# Primary documents of Levent Alpöge's Riemann Hypothesis proof claim (statement `remark.pdf`, Lean archive, and anything else posted)

Research date: Friday 20 November 2026. All fetch times below are UTC on that date, from my own downloads.
Everything in this file is **the author's claim as written in his documents**, or my own mechanical description of the files he posted. Nothing here is independent confirmation that the mathematics is correct. I did not compile the Lean code.

Documents read (complete list):

| Document | URL | Fetched (UTC) | What it is |
|---|---|---|---|
| Statement | https://alpo.ge/remark.pdf | 14:34:09 (re-fetched 14:41:10, identical) | 4-page LaTeX PDF, untitled, unsigned, no date printed; PDF metadata CreationDate = ModDate = Fri 20 Nov 2026 12:52:48 UTC; 245,114 bytes; SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |
| Lean archive | https://alpo.ge/lean.tar.gz.part01 … https://alpo.ge/lean.tar.gz.part14 | 14:35:58–14:36:00 | 14 split parts of one gzip'd tar; 239,275,554 bytes joined; SHA-256 of joined file `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |
| Author home page | https://alpo.ge/ | 14:34:10 | Personal page; contains no mention of or link to the claim |
| arXiv author query | https://export.arxiv.org/api/query?search_query=au:Alpoge&sortBy=submittedDate&sortOrder=descending&max_results=8 | 14:34:58 | No November 2026 posting |
| Scientific American article (pointer only) | https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/ | ~14:35 | Links to `remark.pdf` only |

There is **no prose mathematical paper, no arXiv preprint, no GitHub repository and no README**. The only mathematical artefact posted is the Lean source archive; the only prose is the 4-page statement.

---

## 1. What does the full text of https://alpo.ge/remark.pdf say?

### Takeaway
The statement is a 4-page personal note in three parts (an unnumbered opening page, a section "1" on timing/acknowledgements, a section "2" giving a 20-item dated "rough timeline Claude provided"). Its core sentence is "I believe I have, working with Claude, discovered a proof¹ of the Riemann Hypothesis", where footnote 1 is nothing but the 14 URLs of a Lean archive; it gives no theorem statement, no proof, and explicitly declines to post a prose write-up.

### Cited Findings

**Physical description.** 4 pages, US letter, produced by pdfTeX 1.40.29 / "LaTeX with hyperref"; Title, Author, Subject fields empty; no title, author name, date or signature appears anywhere in the text; the only hyperlinks embedded in the PDF are the footnote-1 URLs. — [remark.pdf](https://alpo.ge/remark.pdf)

**Page 1 (unnumbered opening), verbatim, seven paragraphs** — [remark.pdf, p. 1](https://alpo.ge/remark.pdf):

> The Riemann Hypothesis is the classic problem in number theory. It asks for optimal control on the count of prime numbers of a given size. Its shadows have guided mathematicians for 150 years, and its many rhymes and reflections, even reaching physics, taught us the unity of our fields.

> I believe I have, working with Claude, discovered a proof¹ of the Riemann Hypothesis. In fact, the method easily extends much further, resolving the so-called Generalized Riemann Hypothesis, and I expect, with more time, the Extended Riemann Hypothesis too. Claude and I have also formalized the arguments without assumptions. It is natural to feel that this is an end, in my case a loss of a principal guiding light, but what I saw during the course of progress so amazed me that I believe it is one dawn across science of something far greater.

> It was my secret in my student days that my plans were for this problem in decades, which meant then that I tried to become familiar with all tools that I could possibly recognize in the problem when it was time. Claude and I have had a great time together with such breadth in recent months, but this time Claude far outpaced me near the finish line. No, Claude flew, and danced, and sparkled near that finish line. I had us on the line of combining two quite different ideas present in a toy setting, one of which was already new and shocking, making very simple one of the shadows of Riemann over which we mathematicians felt most triumph. I guided us to the right situation analogous to that toy setting, and then Claude began to leave me in awe.

> Tens of such occurred, but I will give one line which will suffice to make fellow mathematicians fall out of their chairs. In Stepanov's argument resolving Riemann over function fields one uses a divisor involving multiplicity. This argument is a descendant of Stepanov's, but multiplicity is hard to find over the integers, corresponding to something like differentiating whole numbers. The simple, new, Fourier-analytic ideas in the toy setting led us to examine chaining theta lifts if we were to have the same tricks recur but work in a natively automorphic manner. The line: for the von Mangoldt sum of length X, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was √X. (And yet, what else could it be?)

> An astounding amount of mathematics is present in the argument, far more than I had imagined would be necessary as a student. My intuition insists it will be massively simplified, likely immediately. But I hope in having the experience of seeing all of number theory's beauty brought together I am just one of the first, and those who love the mathematics will all be able to enjoy such transcendence in the future.

> The argument is incredibly long at the moment, and while its formalization is finished and it is routine to produce a huge, unreadable document containing sufficient detail, in my view of my path I have just taken a step. I intend to do my best to understand and impart understanding of this argument and its certain simplifications, to speak about it, to write it properly.

> In a time of revolution in mathematics I hope the argument provides a glimpse towards the miracles that lie ahead, and shows us the joy and wonder we are about to find in the simplest things.

**Footnote 1 (attached to the word "proof"), verbatim, in full:** "https://alpo.ge/lean.tar.gz.part01, . . . , https://alpo.ge/lean.tar.gz.part14." — [remark.pdf, p. 1 fn. 1](https://alpo.ge/remark.pdf). The footnote contains no words, only the two hyperlinked URLs and an ellipsis.

**Section "1" (page 2), verbatim, five paragraphs** — [remark.pdf, p. 2](https://alpo.ge/remark.pdf):

> It is obvious to me that I should remark on the following.

> The precise timing is horrible. If I could have, I'd have finished this all much earlier. Hell, strictly before this age would have sure been nice. This all happened for me late Sunday night, and I messaged Dario, "Hypothetically, if I were to have . . . ", eventually asking about my ability to announce. We went and figured it out and the fact is that there was a constraint to respect, though I did ask about progressively more bizarre ideas. This problem has been *the* sacred object in mathematics for me since my childhood, and I am very touchy about the treatment of great intellectual goals, though seriously imperfect. Our leadership and the few trusted mathematicians I consulted hold extremely similar views on the right things to do in these circumstances (it is occasionally possible for physicists and mathematicians to agree. . . ), and I am clearly unilaterally responsible for feeling I just could not live if I waited even longer. There is an obvious cynical view, to do with the timing, but it is false, and I am pleased that I am in circumstances where it is obviously false.

> This puts us in the rather extraordinary situation this age has made possible, in which I am presenting the world with a complete argument before having mastered a massive neighbourhood around its mathematics. It being obviously inappropriate to attempt to post some massive unreadable travesty of "slop"², I decided to only present Lean.

> In a different vein, I have a lot of people I want to praise, and I will do a proper job in a proper writeup, alas pardon the accidental omissions — among many others, Manjul Bhargava, Kai Gill, Hamish Kerr, Max Leiter, John Ma, Tal Magdish, Chris Paika, Maksym Radziwiłł, Jascha Sohl-Dickstein, Peter Sarnak, Jarred Sumner, Amir Tajdini, and especially David Dohan, Ben Michel, Ralph Furman, Eric Price, and Cora Vinther, and my miraculous colleagues. I want them to be proud.

> I have benefited from the good taste of the people at OpenAI involved with various mathematical results, so I am quite happy to praise them too. The Ehrhart conjecture was one such tasteful choice some time ago; playing further and working out the equality case I saw accurate handling of solutions of the Monge-Ampère equation and immediately understood Navier-Stokes was going to fall. Similarly, their quiet inclusion of the Siegel argument, whose result was strictly dominated by the (2, 3, 6)-triangle group trick, again showed great taste; though I did not comment so publicly, I immediately recognized it as Stepanov without multiplicity, though it was only clear to me during this rather harebrained tornado through the whole of number theory that this problem would fall given enough all-nighters and physical toll when I had the qN = M^k + R sign-only proof of Weil and Deligne.

**Footnote 2 (attached to "slop"), verbatim:** "I of course amused myself, and hit 250, 000+ pages. Claude cutely called it the GRH . . . "book" — I looked at Theorem 1 and it began by noting that because the reals are totally ordered if σ ≠ 1/2 then σ > 1/2 or σ < 1/2." — [remark.pdf, p. 2 fn. 2](https://alpo.ge/remark.pdf)

**Section "2" (pages 3–4), opening paragraph verbatim** — [remark.pdf, p. 3](https://alpo.ge/remark.pdf):

> I had a stream-of-consciousness jaunt through the experience of finding all the pieces of the argument through incredible confusion with Claude, but a trusted mathematician advised me to just get to the point and have some sort of timeline. I emphasize that once we saw multiplicity 2 on O(2, n) via the "natively-automorphic" determinant that I'd been searching for via analogy to the definite sign of the left-hand side of³ qN = M^k + R meaning holo/automorphy over a function field, winning more multiplicity with more theta lifts, we were going to win but I was also, so to speak, out of my element, in that I personally have little mastery of automorphic forms on higher rank groups (youthful foolish stubbornness). I also emphasize that I may have baked lots of strange suboptimal choices into the argument, and expect short arguments to follow fairly quickly, though I have not had time to search for such myself (yet!).
> So here is a rough timeline Claude provided after a thorough search.⁴

**The 20-item timeline, verbatim** (dates are in US month/day/year form; formulas transcribed from the rendered page; list order is the document's and is not chronological) — [remark.pdf, pp. 3–4](https://alpo.ge/remark.pdf):

1. "10/6/26: Stepanov determinant."
2. "10/9/26: D^p ≡ 0 on a CM curve for p inert in K, D the invariant derivation, and D^a·θ(0)/Ω^a is divisible by p^(a/p + a/p³ + ··· − O(log a))."
3. "10/19/26+: qN = M^k + R, using x₁·x₂ + ··· + x_{k−1}·x_k, wanting "automorphy" of N since µ is automorphic from θ on sixfold cover of GL₅ as a period integral of thetas, quadric has natural interpretation on corresponding CM e.g. ℂ/ℤ[ω] as Weil⁵, put Poincaré bundle on the edges to get θs."
4. "10/6/26+: W(𝟙_S) ≥ 0 via a determinant, interpret as Stepanov with multiplicity one again; bootstrap!!"
5. "10/20/26: definitively switch to Λ aka Σ_{n≤X} Λ(n)·(X/n − 1)₊ − X log X + (1 + γ)·X; Guinand-Weil had the sign, variance test function trick to make things look trace-formula-like (but how can I pigeonhole / Turán over n? X? it?), Mehta-like integral over twists or at infinity. . ."
6. "10/8/26: W(𝟙_(0,1] + (∼ X^η)·𝟙_(0,1/X]) ≥ 0 gives > 1 − η."
7. "10/14/26: Determinants for W(·)'s containing the desired periods, indeed GGP periods, with values 0, 1 meaning interlacing weights, or up to m non-interlacing ones."
8. "11/15/26: Iterated theta lifts U(X₀) → U(X₁) → ··· → U(X_m) between totally definite unitary groups, π ↦ π ⊞ µ_j[t], wins multiplicity m. Time to take m like √X. . ."
9. "11/15/26: Norms of the lifts and level and cancellation of order-m terms with proven divisibility via Chowla-Selberg, Weyl, and Siegel mass."
10. "11/15/26: Sufficient lower bound on divisibility of the m-fold iterated lift."
11. "10/6/26: Iwasawa tower via analogy to pigeonhole on F_{qⁿ}/F_q."
12. "11/15/26: Seesaw: the period of the iterated lift is a Bessel period independent of the Hecke characters, Rallis."
13. "10/6/26: Bost slope inequality."
14. "11/15/26: precise computation of the "cost" of each lift, showing that one would stop at 2/3 a priori, attempt to get a main term and transfer constant to a function field or kill via twisting, need for "division"."
15. "11/15/26: Glue together an integral structure across Hecke characters for a "gcd" i.e. extra averaging."
16. "10/14/26: Relative trace formula, seen in a different half-plane argument via sixfold cover of GL₅ automorphy of µ and reducing via Cauchy-Schwartz to a bound on the norm of a suitably projected Poincaré series, approximate orthogonality of the columns of the integral structure."
17. "11/15/26: for the classes in H¹(𝔬_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) that we couldn't kill by twisting, fight for a significant weakening of Vandiver.⁶"
18. "11/15/26: computation of covolumes, theta series' index, congruences between lifts and forms."
19. "10/19/26: precise choice of the Iwasawa tower, specifically using Behrend!!⁷"
20. "11/16/26: GRH."

**Footnote 3 (to "qN = M^k + R"), verbatim** — a displayed sum "Σ_{h,x₁,...,x_k} t(x₁)···t(x_k)·e_q(h(x₁·x₂ + ··· + x_{k−1}·x_k))," followed by: "sum over h first for the left-hand side, with e.g. quadric coefficients too Bertini gives a definite sign from middle cohomology, one off the one on M^k, which is the zero-mode on the right-hand side with R square-root-quality up to an inch or so as Katz would say by iterating Parseval k times, opposite signs meaning no cancellation of inverse roots, QED; vectorize to go up dimensions. Gabber's hypersurface in one of Katz's arguments reminds one of the quadric, which comes from looking for a simplification of averaging over the family χ ↦ χ(disc), corresponding to a ↦ y(·)^a with y the normalized Gauss sum of order #|µ_K| who lives via θ on the #|µ_K|-fold cover of GL₂, the reciprocity law of y(c·c′) vs. y(c)·y(c′) showing some sort of complete graph, simplifying to the above "path" quadric, Gauss sum cancellation replaced by iterated Parseval." — [remark.pdf, p. 3 fn. 3](https://alpo.ge/remark.pdf)

**Footnote 4 (to "a rough timeline Claude provided after a thorough search"), verbatim:** "The parts in which my vague intuition worked out due to Claude's technical mastery are of course less familiar to me today, and probably I'll have to edit some of these descriptions on reflection. The parts in which Claude is the expert and not me I am sort of paraphrasing a "slop" summary, which might make zero sense, and I apologize, though the Lean should suffice to clarify everything. I'm just too inexpert in the relevant stuff at the moment, I hope the reader sees the breadth of this argument!" — [remark.pdf, p. 3 fn. 4](https://alpo.ge/remark.pdf)

**Footnote 5 (to "as Weil"), verbatim:** "A lot is obviously being lossily compressed here, but especially after gritting with Sussman through Bałaban's fantastic induction I had to think to myself about how hard fighting for some sort of F₁ à la e.g. Borger would be." — [remark.pdf, p. 3 fn. 5](https://alpo.ge/remark.pdf)

**Footnote 6 (to "weakening of Vandiver"), verbatim:** "This is still pretty strong!! I believe vanishing of a number of K-groups of ℤ follows, and cyclicity up to 100ish maybe? I had Lichtenbaum, so I knew we would have a lot of slack in fighting these K's." — [remark.pdf, p. 4 fn. 6](https://alpo.ge/remark.pdf)

**Footnote 7 (to "specifically using Behrend!!"), verbatim:** "This is the sort of trick that intuitively to me is obviously going to be unnecessary." — [remark.pdf, p. 4 fn. 7](https://alpo.ge/remark.pdf)

**Paragraph-by-paragraph summary** (all from [remark.pdf](https://alpo.ge/remark.pdf)):
- p. 1 ¶1: one-sentence description of RH and its influence.
- p. 1 ¶2: the claim (RH; method "resolving" GRH; ERH "expect[ed], with more time"); formalization "without assumptions"; emotional reaction.
- p. 1 ¶3: student-days plan; "recent months" working with Claude; Claude "far outpaced me near the finish line"; author supplied the line of attack (combining two ideas from a "toy setting") and "guided us to the right situation analogous to that toy setting".
- p. 1 ¶4: the one mathematical "line" offered: argument is "a descendant of Stepanov's"; multiplicity is replaced by chains of theta lifts; chain length √X for a von Mangoldt sum of length X was "Claude's suggested" choice.
- p. 1 ¶5: argument uses far more mathematics than expected; author predicts massive simplification.
- p. 1 ¶6: argument "incredibly long"; formalization "finished"; author has "just taken a step" and intends to understand, speak about and "write it properly".
- p. 1 ¶7: closing hope.
- §1 ¶1–2: timing; contacted "Dario" late Sunday night; an unnamed "constraint to respect"; decision to announce is his "unilateral" responsibility; denies an unnamed "obvious cynical view, to do with the timing".
- §1 ¶3: he is presenting "a complete argument before having mastered a massive neighbourhood around its mathematics"; "decided to only present Lean" rather than a machine-generated prose document (fn. 2: he generated one of "250, 000+ pages").
- §1 ¶4: acknowledgements (17 named people plus "my miraculous colleagues"); a "proper writeup" is promised.
- §1 ¶5: praise for OpenAI-associated mathematical results (Ehrhart conjecture; "the Siegel argument"), which he says he recognized as "Stepanov without multiplicity".
- §2: admits he is "out of my element" on "automorphic forms on higher rank groups"; warns of "strange suboptimal choices"; gives the 20-item timeline "Claude provided".

### Inferences
- "Late Sunday night" most naturally means Sunday 15 November 2026 (twelve of the twenty timeline items are dated 11/15/26, and item 20 "GRH" is dated 11/16/26, a Monday); the document does not state the date explicitly.
- "Dario" is presumably Dario Amodei (Anthropic's CEO); the statement gives only the first name. "Our leadership" presumably means Anthropic's; the statement never names Anthropic.
- The timeline dates run from 6 October 2026 to 16 November 2026, i.e. about six weeks; the PDF was compiled four days after the last date (20 Nov 2026 12:52:48 UTC per PDF metadata).
- The document reads as a personal announcement, not a mathematical paper: it has no theorem statement, definitions, or proof, and footnote 4 concedes parts of the timeline are a paraphrase of a Claude summary "which might make zero sense".

### Gaps
- The statement never defines W(·), N, M, R, µ, t, or the "toy setting"; it cannot be reconstructed from the text what the argument actually is.
- The "constraint to respect" and the "obvious cynical view, to do with the timing" are not explained.
- No time of posting is given in the document; the earliest evidence I have is the PDF build time (12:52:48 UTC) and a Wayback Machine capture timestamped 14:19:58 UTC ([Wayback availability API](https://archive.org/wayback/available?url=alpo.ge/remark.pdf)).

---

## 2. Exactly which statements are claimed (RH, GRH for which L-functions, ERH)?

### Takeaway
In prose the author claims RH ("I believe I have ... discovered a proof"), says the method resolves "the so-called Generalized Riemann Hypothesis", and only "expect[s], with more time" the "Extended Riemann Hypothesis"; none of the three is defined in the statement. The only precise statements are in the Lean archive's `Statements.lean`/`Main.lean`: RH for the Riemann zeta function, and non-vanishing for Re s > 1/2 / zeros-on-the-line in 0 < Re s < 1 for the L-function of **every Dirichlet character of every modulus** — nothing about Dedekind zeta functions, Hecke L-functions or automorphic L-functions appears among the top-level theorems.

### Cited Findings
- Prose claim, verbatim: "I believe I have, working with Claude, discovered a proof¹ of the Riemann Hypothesis. In fact, the method easily extends much further, resolving the so-called Generalized Riemann Hypothesis, and I expect, with more time, the Extended Riemann Hypothesis too." — [remark.pdf, p. 1](https://alpo.ge/remark.pdf)
- The last timeline entry is "11/16/26: GRH." (not "RH"), and footnote 2 says Claude called the generated prose document "the GRH . . . "book"". — [remark.pdf, p. 4 and p. 2 fn. 2](https://alpo.ge/remark.pdf)
- The statement nowhere says which L-functions "Generalized" or "Extended" refer to; the words "Dirichlet", "Dedekind", "Artin" and "automorphic L-function" do not occur in it ("Hecke characters" occurs in timeline items 12 and 15 as part of the method, not as a class of L-functions for which a hypothesis is claimed). — [remark.pdf](https://alpo.ge/remark.pdf)
- The Lean archive's file `lean/src/Statements.lean` (783 bytes) defines exactly four propositions, verbatim — [Lean archive](https://alpo.ge/lean.tar.gz.part01):

```lean
import Mathlib

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

- The file `lean/src/Main.lean` (433 bytes) states five top-level theorems, with no hypotheses, verbatim — [Lean archive](https://alpo.ge/lean.tar.gz.part01):

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

- `RiemannHypothesis` is not defined anywhere in the archive (my search for a definition found none), so it refers to the proposition of that name in the pinned Mathlib; the archive itself proves `Claim.zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl`, where `Claim.Zeta` is "∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2". — [Lean archive, `src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean` and `ClaimStrip.lean`](https://alpo.ge/lean.tar.gz.part01)
- In the Lean, everything is derived from one proposition, `UpperTheory.EveryCharacter` := "∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0"; RH for zeta is obtained as the case N = 1 (`Formalism.VW.rh_of_every`), and the "zeros on the line" forms are obtained from it by the functional equation (`Claim.strip`, `Formalism.VW.critLine`). — [Lean archive, `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean`, `src/Supplements/Kernels/MainTheorems.lean`](https://alpo.ge/lean.tar.gz.part01)
- Neither `Main.lean`, `Statements.lean` nor the three files in `src/Supplements/Kernels/` mention `dedekindZeta`, Hecke characters or Grössencharacters (search returned nothing). A directory `src/Development/AutomorphicArithmetic/DedekindLFunctions` exists inside the development, but no top-level theorem about Dedekind zeta zeros is stated. — [Lean archive](https://alpo.ge/lean.tar.gz.part01)
- `Supplements/Kernels/MainTheoremsCritical.lean` and `MainTheoremsAll.lean` additionally import a folder `SmallClassNumbers` containing auxiliary results not about zeros, e.g. `theorem classNumber_three : classNumber (Kstar 3) = 1`, `theorem bound : Bound`, and `theorem len_eq_zero_iff : len Ω l c e = 0 ↔ Vanish Ω l c e` (statements about lengths/vanishing of Galois-cohomology classes twisted by a power `−e` of the cyclotomic character, for primes l ≥ 5 with ¬(l − 1 ∣ 2e), e even). — [Lean archive, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/`](https://alpo.ge/lean.tar.gz.part01)

### Inferences
- The precise content of the claimed "Generalized Riemann Hypothesis" is therefore GRH **for Dirichlet L-functions** (all characters, primitive or not, all moduli), in the form "no zeros with Re s > 1/2" plus "all zeros in the open critical strip have Re s = 1/2". This is the usual textbook meaning of "GRH" in analytic number theory, but it is narrower than GRH for automorphic L-functions.
- "Extended Riemann Hypothesis" is conventionally the statement for Dedekind zeta functions of number fields; the statement does not say so, and by its own wording this is only "expect[ed], with more time" — i.e. **not claimed as proved** and not present among the Lean top-level theorems.
- The `SmallClassNumbers` results look like the Lean counterpart of timeline item 17 and footnote 6 ("a significant weakening of Vandiver"); that identification is mine, not the author's.

### Gaps
- No prose statement of a main theorem exists; the only formal statements are the Lean ones above.
- Whether the Lean statements faithfully capture RH/GRH depends on Mathlib's definitions of `riemannZeta`, `DirichletCharacter.LFunction` and `RiemannHypothesis` at the pinned commit (`0df444a360eaa60ab8c11dca51a86af692955474`); I did not inspect that Mathlib commit.
- The author does not say whether ERH/Dedekind, Hecke or automorphic cases are in progress, or what obstacle remains.

---

## 3. Is there a mathematical paper or proof write-up? Title, authors, length, date, URL, abstract, structure, method, tools, key new idea

### Takeaway
No. As of 14:41 UTC on 20 November 2026 there is no paper, no arXiv preprint, no abstract and no README: the author "decided to only present Lean", and the proof exists publicly only as a ~1.03 GB, 175,187-file, 17.4-million-line Lean 4 source tree with no comments or documentation. The method is described only impressionistically: "a descendant of Stepanov's" function-field argument in which "multiplicity" is supplied by a chain of about √X iterated theta lifts between totally definite unitary groups.

### Cited Findings

**Absence of a write-up**
- "It being obviously inappropriate to attempt to post some massive unreadable travesty of "slop"², I decided to only present Lean." — [remark.pdf, p. 2](https://alpo.ge/remark.pdf)
- A machine-generated prose version exists privately: "I of course amused myself, and hit 250, 000+ pages. Claude cutely called it the GRH . . . "book"". — [remark.pdf, p. 2 fn. 2](https://alpo.ge/remark.pdf)
- "it is routine to produce a huge, unreadable document containing sufficient detail"; a "proper writeup" is promised without a date ("I will do a proper job in a proper writeup"; "to write it properly"). — [remark.pdf, pp. 1–2](https://alpo.ge/remark.pdf)
- The arXiv API author query `au:Alpoge`, sorted by submission date, returned as its newest entries 2609.16470 (15 Sep 2026), 2609.02606 (2 Sep 2026) and 2608.13637v2 ("More than two thirds of the zeta zeros are simple and on the critical line", published 13 Aug 2026, updated 19 Aug 2026); there is no entry from November 2026 and none claiming RH. — [arXiv API query](https://export.arxiv.org/api/query?search_query=au:Alpoge&sortBy=submittedDate&sortOrder=descending&max_results=8)
- The author's home page, fetched 14:34:10 UTC, does not mention the Riemann Hypothesis, does not link `remark.pdf` or the Lean parts, and still says "the most recent paper is a solution of hilbert's tenth problem (posed in 1900) over all number fields"; its paper list ends at item 22 (the Hilbert's tenth problem paper). Its sub-pages `fun/`, `recent recorded talks/` and `amusing math history links/` contain no occurrence of "riemann", "remark.pdf", "lean.tar", "claude" or "grh". — [alpo.ge](https://alpo.ge/)
- The Scientific American article links only `https://alpo.ge/remark.pdf` as a primary document and says "Alpöge posted his Claude proof coded in the programming language Lean" (retrieved through a summarizing fetch tool, so treat the wording as approximate). — [Scientific American, 20 Nov 2026](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)

**The Lean archive, described mechanically (my own inspection of the downloaded files; not verification)** — all from [the 14 parts starting at lean.tar.gz.part01](https://alpo.ge/lean.tar.gz.part01):
- Parts 01–13 are exactly 18,000,000 bytes each; part 14 is 5,275,554 bytes; concatenated in order they form a valid gzip (passes `gzip -t`) of a tar archive.
- The tar holds 175,190 regular files under a single directory `lean/`: `lean/lake-manifest.json`, `lean/lakefile.toml`, `lean/lean-toolchain`, and 175,187 `.lean` files under `lean/src/`. Uncompressed size 1,030,536,719 bytes; 17,374,215 lines of Lean. Every file's modification time is zeroed (1970-01-01 00:00), owner 0/0, so the archive carries no internal dates.
- `lean-toolchain`: "leanprover/lean4:v4.33.1". `lakefile.toml`: package `name = "tree"`, `srcDir = "src"`, one dependency, Mathlib at `rev = "0df444a360eaa60ab8c11dca51a86af692955474"`, `maxHeartbeats = 4000000`, `moreLeanArgs = ["--tstack=400000"]`; libraries `BuildAid`, `CompanionTheory`, `Development`, `Formalism`, `GroundTheory`, `GroundTheoryFields`, `Lemmata`, `PositivityTheory`, `ReciprocityTheory`, `Supplements`, `Main` (roots `Statements`, `Main`).
- File counts / bytes by top-level folder: `Development` 141,928 files / 767,288,236 bytes; `Formalism` 18,254 / 164,903,481; `GroundTheory` 8,507 / 54,564,791; `ReciprocityTheory` 3,845 / 28,914,051; `CompanionTheory` 2,027 / 11,296,366; `PositivityTheory` 449 / 3,109,326; `Lemmata` 167 / 452,342; `BuildAid` 5 / 850; `Supplements` 3 / 1,195; plus `Main.lean` and `Statements.lean`.
- Largest second-level folders by file count: `Development/AbelianVarietyTheory` 99,187; `Development/AutomorphicArithmetic` 18,431; `Development/AutomorphicSpectrum` 15,147; `Development/WeilBound` 7,051; `GroundTheory/HeightsAndTheta` 6,410; `Formalism/LocalToGlobal` 5,501; `Formalism/PeriodIntegrals` 4,350; `Formalism/SharpRestriction` 3,093; `ReciprocityTheory/ReductiveGroups` 2,799; `Formalism/HermitianCurvature` 1,922; `Development/EtaleCohomology` 1,398; `CompanionTheory/SpectralGeometry` 1,254.
- Approximate declaration counts by text search: 813,194 lines beginning `theorem`/`lemma`; 241,088 beginning `def`/`abbrev`/`structure`/`class`/`instance`/`inductive`.
- The tree contains **no documentation at all**: no README, no non-Lean files beyond the three build files, zero `--` line comments, zero `/-` block or doc comments, and zero occurrences of the strings "Claude" or "Anthropic". 136,003 files begin with a blanket `import Mathlib`.
- Folder names indicating subject matter include (under `Development/AutomorphicArithmetic/ThetaCorrespondence`) `BesselModels`, `HoweDuality`, `RallisInnerProduct`, `ThetaPairLifts`, `WeilRepresentation`, `LocalLanglands`, `PrismaticDieudonne`, `CrystallineComparison`; (under `Development/WeilBound`) `ThetaLifts`, `KatoCoprimality`, `CoreStatements/PadicHodgeComparison`, `CoreStatements/ResolutionCharZero`; (under `Development/AbelianVarietyTheory/Proofs`) `SiegelThetaTransformation`, `IwasawaDecomposition`, `ToricGeometry`, `CovolumeBounds`; also `Development/EtaleCohomology`, `Development/ResolutionOfSingularities`, `Formalism/LandauZeroFreeBounds`, `Formalism/ZeroFreeRegion`, `Formalism/HarderNarasimhan`, `Formalism/LatticeSlopes`, `ReciprocityTheory/ClassFieldTheory`, `ReciprocityTheory/Chebotarev`, `GroundTheory/PAdicHodge`.
- File-name matches for terms from the statement's timeline: "ThetaLift" 472 files, "Seesaw" 452, "Bessel" 881, "Iwasawa" 269, "Slope" 209, "Poincare" 179, "Kato" 129, "Mangoldt" 16, "ChowlaSelberg" 9, "SiegelMass" 8, "GanGrossPrasad" 6, "IteratedTheta" 4, "Behrend" 3, "RelativeTrace" 2; "Stepanov" 0 and "Vandiver" 0 (neither word occurs anywhere in the tree).
- The proof term of the final theorem passes through `UpperTheory.FinalTheorems.everyCharacter`, defined in `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` as `everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`, which in turn calls `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (file `.../ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`); that lemma's body names inputs such as `theta_integrals_agree_and_local_matching_of_literature`, `resolution_char_zero_of_literature`, `principalisation_char_zero_of_literature`, `poincare_lelong_inv_of_literature`, `fargues_exact_of_literature`, `zarhin_statement`, `nef_rr_of_literature`, `siegel_toroidal_integral_of_literature`, `grothendieck_deformation_of_literature`, `local_langlands_gl_recT_exists_of_literature`, and `HilbertSamuelMoriwaki.hsUse_outright`.

**Method, tools and "key new idea" as the author describes them** (all from [remark.pdf](https://alpo.ge/remark.pdf)):
- Lineage: "In Stepanov's argument resolving Riemann over function fields one uses a divisor involving multiplicity. This argument is a descendant of Stepanov's, but multiplicity is hard to find over the integers, corresponding to something like differentiating whole numbers." (p. 1)
- Key idea he singles out: "The simple, new, Fourier-analytic ideas in the toy setting led us to examine chaining theta lifts if we were to have the same tricks recur but work in a natively automorphic manner. The line: for the von Mangoldt sum of length X, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was √X." (p. 1); and in the timeline, "Iterated theta lifts U(X₀) → U(X₁) → ··· → U(X_m) between totally definite unitary groups, π ↦ π ⊞ µ_j[t], wins multiplicity m. Time to take m like √X. . ." (item 8).
- Origin in a "toy setting": "combining two quite different ideas present in a toy setting, one of which was already new and shocking, making very simple one of the shadows of Riemann over which we mathematicians felt most triumph" (p. 1); §1 and fn. 3 identify this as "the qN = M^k + R sign-only proof of Weil and Deligne" over finite fields, argued via "a definite sign from middle cohomology", "iterating Parseval k times", "opposite signs meaning no cancellation of inverse roots, QED".
- Turning point: "once we saw multiplicity 2 on O(2, n) via the "natively-automorphic" determinant that I'd been searching for ... winning more multiplicity with more theta lifts, we were going to win" (p. 3).
- Named tools/earlier results in the timeline and footnotes: Stepanov determinant; CM curves and an invariant derivation with p-divisibility of D^a θ(0)/Ω^a; θ on a "sixfold cover of GL₅"; Poincaré bundle; a positivity functional "W(𝟙_S) ≥ 0 via a determinant"; the weighted von Mangoldt sum Σ_{n≤X} Λ(n)(X/n − 1)₊ − X log X + (1+γ)X; "Guinand-Weil" (explicit formula) "had the sign"; "variance test function trick to make things look trace-formula-like"; "Mehta-like integral"; "GGP periods"; "Chowla-Selberg, Weyl, and Siegel mass"; "Iwasawa tower via analogy to pigeonhole on F_{qⁿ}/F_q"; "Seesaw", "Bessel period", "Rallis"; "Bost slope inequality"; "Relative trace formula"; "Cauchy-Schwartz" [sic] and "a suitably projected Poincaré series"; Galois cohomology classes in H¹(𝔬_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) and "a significant weakening of Vandiver"; "Behrend"; Bertini, Katz, Gabber, Gauss sums on the #|µ_K|-fold cover of GL₂; Lichtenbaum and K-groups of ℤ; Borger-style F₁; Bałaban's induction (pp. 3–4 and fns. 3, 5, 6).
- Intermediate strength noted along the way: item 6 "gives > 1 − η"; item 14 "showing that one would stop at 2/3 a priori, attempt to get a main term and transfer constant to a function field or kill via twisting, need for "division"" (p. 4).
- Claimed by-product: "I believe vanishing of a number of K-groups of ℤ follows, and cyclicity up to 100ish maybe?" (fn. 6) — hedged, not stated as a theorem.
- Not mentioned anywhere in the statement: de Branges spaces, mollifiers, a Hilbert–Pólya operator, or random-matrix theory by name (the only nearby phrase is "Mehta-like integral").

### Inferences
- "W(·) ≥ 0" together with the "Guinand-Weil" reference suggests a Weil-explicit-formula positivity criterion, but the statement never defines W, so this must not be asserted as the author's stated method.
- The Lean folder names (theta correspondence, Bessel models, Rallis inner product, seesaw, p-adic Hodge theory, étale cohomology, resolution of singularities, slopes/Harder–Narasimhan) are broadly consistent with the tools listed in the timeline, but folder names are not evidence about what is actually proved.
- Names such as `..._of_literature` and `PublishedTheorems` suggest that standard published results were first isolated as hypotheses and then supplied; in the final theorem they appear to be discharged by a theorem inside the archive (`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`), since `Main.lean`'s theorems take no hypotheses. I have not traced or compiled this.
- The "2/3" in item 14 is described as the a priori stopping point of the lift "cost" computation; the document does not connect it to Anthropic's August 2026 two-thirds result, and neither that paper nor arXiv 2608.13637 is mentioned anywhere in the statement.

### Gaps
- No human-readable proof exists publicly; the structure of the argument (what is bounded, what the contradiction is, where zeros with Re s > 1/2 are excluded) cannot be extracted from the statement, and I did not attempt to reverse-engineer it from 17.4 million lines of uncommented Lean.
- No title, author list, abstract or length for a paper can be given because none exists. The statement does not say whether Claude will be a co-author of the eventual write-up.
- The 250,000+-page generated "book" is not posted.

---

## 4. What does the author say about how the work was done with Claude?

### Takeaway
The statement says only "Claude" — no model name, version, product, compute budget or number of sessions. The author credits himself with the long-prepared breadth, the toy-setting ideas and steering to "the right situation", and credits Claude with the technical execution near the end ("Claude far outpaced me near the finish line"), with "tens" of awe-inducing steps including the √X chain length, with the automorphic-forms expertise he says he lacks, with co-formalizing the proof, and with writing the timeline.

### Cited Findings
- Model: the word "Claude" appears with no qualifier throughout; there is no mention of a model name/number, of "Anthropic", or of any tool such as Claude Code. — [remark.pdf](https://alpo.ge/remark.pdf)
- Period: "Claude and I have had a great time together with such breadth in recent months" (p. 1); timeline dates run from "10/6/26" to "11/16/26: GRH." (pp. 3–4); "This all happened for me late Sunday night" (p. 2). — [remark.pdf](https://alpo.ge/remark.pdf)
- Author's own role: "I had us on the line of combining two quite different ideas present in a toy setting ... I guided us to the right situation analogous to that toy setting"; "the "natively-automorphic" determinant that I'd been searching for via analogy to ... qN = M^k + R". — [remark.pdf, pp. 1, 3](https://alpo.ge/remark.pdf)
- Claude's role: "this time Claude far outpaced me near the finish line. No, Claude flew, and danced, and sparkled near that finish line"; "then Claude began to leave me in awe"; "Tens of such occurred"; "Claude's suggested length of chain of theta lifts ... was √X." — [remark.pdf, p. 1](https://alpo.ge/remark.pdf)
- Division of expertise: "I was also, so to speak, out of my element, in that I personally have little mastery of automorphic forms on higher rank groups"; "The parts in which my vague intuition worked out due to Claude's technical mastery are of course less familiar to me today"; "The parts in which Claude is the expert and not me I am sort of paraphrasing a "slop" summary, which might make zero sense". — [remark.pdf, p. 3 and fn. 4](https://alpo.ge/remark.pdf)
- Claude also (a) co-formalized: "Claude and I have also formalized the arguments without assumptions" (p. 1); (b) produced the timeline: "a rough timeline Claude provided after a thorough search" (p. 3); (c) produced and named the long prose version: "Claude cutely called it the GRH . . . "book"" (fn. 2). — [remark.pdf](https://alpo.ge/remark.pdf)
- What he "saw during the course of progress": the phrase occurs once — "what I saw during the course of progress so amazed me that I believe it is one dawn across science of something far greater" (p. 1). The statement's only concrete illustrations are the √X chain-length suggestion and the general description that "Claude flew, and danced, and sparkled"; he adds "I am presenting the world with a complete argument before having mastered a massive neighbourhood around its mathematics" (p. 2) and hopes "the argument provides a glimpse towards the miracles that lie ahead" (p. 1). — [remark.pdf](https://alpo.ge/remark.pdf)
- Human mathematicians consulted (role unspecified): "the few trusted mathematicians I consulted"; "a trusted mathematician advised me to just get to the point and have some sort of timeline"; acknowledgement list of 17 names including Manjul Bhargava, Maksym Radziwiłł, Peter Sarnak and Ralph Furman. — [remark.pdf, pp. 2–3](https://alpo.ge/remark.pdf)
- The author's affiliation per his own home page: "pt&rl, anthropic, pbc" and "junior fellow, harvard sof". — [alpo.ge](https://alpo.ge/)

### Inferences
- By his own account the author does not currently understand every part of the argument ("less familiar to me today"; "too inexpert in the relevant stuff at the moment"), so the claim rests on the Lean formalization rather than on his having checked the mathematics by hand.
- The statement is written in the first person singular and presents the result as his discovery "working with Claude"; it does not present Claude as an author, nor describe an autonomous run.

### Gaps
- Which Claude model, whether it was a released or internal model, how it was run (interactive chat, agentic sessions, token counts), and how much human intervention there was at each step are not stated.
- The statement does not say that the acknowledged mathematicians have read or checked the proof.

---

## 5. What does the statement say about formalization ("formalized the arguments without assumptions") and what Lean links does it give?

### Takeaway
The statement asserts that a complete Lean formalization exists ("its formalization is finished"), with "without assumptions" left unexplained, and gives as its sole evidence 14 direct download links `https://alpo.ge/lean.tar.gz.part01` … `part14` (footnote 1 to the word "proof"). The archive is a Lean 4 / Mathlib project whose `Main.lean` states RH and Dirichlet-GRH as hypothesis-free theorems, and a plain-text search finds no `sorry` and no `axiom`; whether it actually compiles and what `#print axioms` reports has **not** been checked by me.

### Cited Findings
- "Claude and I have also formalized the arguments without assumptions." — [remark.pdf, p. 1](https://alpo.ge/remark.pdf)
- "while its formalization is finished and it is routine to produce a huge, unreadable document containing sufficient detail..." — [remark.pdf, p. 1](https://alpo.ge/remark.pdf)
- "I decided to only present Lean." — [remark.pdf, p. 2](https://alpo.ge/remark.pdf)
- "...though the Lean should suffice to clarify everything." — [remark.pdf, p. 3 fn. 4](https://alpo.ge/remark.pdf)
- Links: footnote 1 reads in full "https://alpo.ge/lean.tar.gz.part01, . . . , https://alpo.ge/lean.tar.gz.part14." No GitHub repository, no build instructions, no checksum and no `#print axioms` output are given. — [remark.pdf, p. 1 fn. 1](https://alpo.ge/remark.pdf)
- All 14 part URLs returned HTTP 200 at 14:35–14:36 UTC; the server sends no `Content-Type` or `Last-Modified` for them. Requests for `lean.tar.gz` (unsplit), `lean.tar.gz.part00` and `lean.tar.gz.part15` return the site's home-page HTML, i.e. those files do not exist. — [lean.tar.gz.part01](https://alpo.ge/lean.tar.gz.part01), [lean.tar.gz.part14](https://alpo.ge/lean.tar.gz.part14)
- The top-level theorems in `src/Main.lean` (quoted in section 2) have no hypotheses; e.g. `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`. — [Lean archive](https://alpo.ge/lean.tar.gz.part01)
- My plain-text searches over all 175,187 `.lean` files found: 0 files containing the word `sorry`; 0 files containing the word `axiom`; 0 occurrences of `sorryAx`, `admit`, `native_decide`, `ofReduceBool`, `implemented_by`, `@[extern`, `opaque` declarations or `debug.skipKernelTC`. There are 5 `run_cmd` lines (all in `src/BuildAid/D1–D5.lean`, each adding a name such as "CompanionTheory" or "UpperTheory" to `Lean.LibrarySuggestions.nameDenyListExt`), 4 `elab` and 22 `macro` definitions (tactic shorthands), 2 `partial`/`unsafe` `def`s, 1,877 uses of `set_option backward.isDefEq.respectTransparency false`, 37 of `set_option allowUnsafeReducibility`, and 57,556 `set_option maxHeartbeats` lines. — [Lean archive](https://alpo.ge/lean.tar.gz.part01)
- Scientific American's only comment on checking: "Issues can arise in Lean, but it shouldn't take long for experts to verify whether the hypothesis is properly coded" (as returned by a summarizing fetch tool). — [Scientific American, 20 Nov 2026](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)

### Inferences
- "Without assumptions" most plausibly means the final Lean theorems carry no unproved hypotheses, `sorry`s or added axioms — in particular that the deep published results the argument uses (the many `..._of_literature` inputs) are themselves formalized rather than assumed. The text-level evidence (no `sorry`/`axiom` strings; hypothesis-free `Main.lean`) is consistent with that reading, but it is the author's claim until someone builds the project and inspects the axioms used.
- Verification burden: compiling ~17.4 million lines against Mathlib is a very large job; the archive ships no build cache (`.lake` is absent) and no instructions, so independent confirmation will take real compute and time.
- A successful build would establish only that the stated Lean propositions follow in Lean's logic from Mathlib's definitions; a separate human check is needed that the definitions used (`riemannZeta`, `DirichletCharacter.LFunction`, `RiemannHypothesis` in the pinned Mathlib commit, and that nothing in the tree shadows them) mean what they should.

### Gaps
- I did not compile the project or run `#print axioms`; nothing here confirms that it type-checks.
- The statement does not say how long the formalization took, how it was produced (which model, how much autonomy), who else has built it, or on what hardware.
- The date of the pinned Mathlib commit could not be looked up (GitHub API access was not available in this session).

---

## 6. What does the author say about himself, next steps, review by others, and uncertainty?

### Takeaway
He frames RH as a lifelong goal ("my secret in my student days that my plans were for this problem in decades"; "the sacred object in mathematics for me since my childhood"), hedges the claim once ("I believe I have"), expects the proof to be "massively simplified, likely immediately", and commits to understanding, lecturing on and properly writing up the argument. He reports consulting Anthropic leadership and "a few trusted mathematicians" about how to announce, but the statement reports **no review of the proof by anyone**.

### Cited Findings
- Student-days plan: "It was my secret in my student days that my plans were for this problem in decades, which meant then that I tried to become familiar with all tools that I could possibly recognize in the problem when it was time." — [remark.pdf, p. 1](https://alpo.ge/remark.pdf)
- Personal stakes: "in my case a loss of a principal guiding light"; "This problem has been *the* sacred object in mathematics for me since my childhood, and I am very touchy about the treatment of great intellectual goals, though seriously imperfect." — [remark.pdf, pp. 1–2](https://alpo.ge/remark.pdf)
- Self-assessed limits: "I personally have little mastery of automorphic forms on higher rank groups (youthful foolish stubbornness)"; "I'm just too inexpert in the relevant stuff at the moment". — [remark.pdf, p. 3 and fn. 4](https://alpo.ge/remark.pdf)
- Uncertainty/hedges: "I believe I have ... discovered a proof"; "I expect, with more time, the Extended Riemann Hypothesis too"; "I may have baked lots of strange suboptimal choices into the argument"; "probably I'll have to edit some of these descriptions on reflection"; the timeline paraphrase "might make zero sense"; "I believe vanishing of a number of K-groups of ℤ follows, and cyclicity up to 100ish maybe?" — [remark.pdf, pp. 1, 3, 4](https://alpo.ge/remark.pdf)
- Unhedged assertions sit alongside these: "the method easily extends much further, resolving the so-called Generalized Riemann Hypothesis"; "its formalization is finished"; "I am presenting the world with a complete argument". — [remark.pdf, pp. 1–2](https://alpo.ge/remark.pdf)
- Next steps: "I intend to do my best to understand and impart understanding of this argument and its certain simplifications, to speak about it, to write it properly."; "I will do a proper job in a proper writeup"; "expect short arguments to follow fairly quickly, though I have not had time to search for such myself (yet!)"; "My intuition insists it will be massively simplified, likely immediately." — [remark.pdf, pp. 1–3](https://alpo.ge/remark.pdf)
- On the decision to announce: "I messaged Dario, "Hypothetically, if I were to have . . . ", eventually asking about my ability to announce. We went and figured it out and the fact is that there was a constraint to respect"; "Our leadership and the few trusted mathematicians I consulted hold extremely similar views on the right things to do in these circumstances ... and I am clearly unilaterally responsible for feeling I just could not live if I waited even longer."; "There is an obvious cynical view, to do with the timing, but it is false, and I am pleased that I am in circumstances where it is obviously false." — [remark.pdf, p. 2](https://alpo.ge/remark.pdf)
- Review: the statement contains no sentence saying any other person has read, checked or endorsed the proof or built the Lean code; the consulted mathematicians are mentioned only in connection with "the right things to do in these circumstances" and with advice to "just get to the point and have some sort of timeline". — [remark.pdf, pp. 2–3](https://alpo.ge/remark.pdf)
- The home page's self-description (unchanged, not about this claim): "i think im an old school mathematician"; "then gpt 4 came out and to me it was instantly the most interesting thing humanity had ever created. back to cs!"; "hi from anthropic!". — [alpo.ge](https://alpo.ge/)

### Inferences
- "I am clearly unilaterally responsible for feeling I just could not live if I waited even longer" reads as saying that announcing now, before a write-up and before mastering the argument, was his own choice and possibly earlier than those he consulted would have preferred; the statement does not say that outright.
- The confidence of the claim is anchored in the Lean formalization, not in peer review or in the author's own line-by-line understanding.

### Gaps
- No timetable for the write-up, talks, journal submission or arXiv posting.
- No statement from Anthropic, and none from any of the acknowledged mathematicians, was found among the primary documents; web searches at ~14:35 and ~14:39 UTC surfaced only material about the separate August 2026 result.
- What the "constraint" on announcing was, and what "the timing" refers to, are unstated.

---

## 7. Have the documents been revised, withdrawn or annotated since first posting?

### Takeaway
No revision, withdrawal or annotation is visible as of 14:41 UTC on 20 November 2026. The statement PDF carries a single build timestamp (20 Nov 2026 12:52:48 UTC), has no version number or changelog, and was byte-identical on two fetches seven minutes apart; the author does, however, pre-announce that the timeline descriptions will probably be edited.

### Cited Findings
- PDF metadata: CreationDate and ModDate both "Fri Nov 20 12:52:48 2026 UTC"; no version label, date line or revision note in the text. — [remark.pdf](https://alpo.ge/remark.pdf)
- Fetched 14:34:09 UTC and again 14:41:10 UTC: same SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`; server ETag `"e447a79e04d634f9391306d44d3f1561"`; no `Last-Modified` header is sent. — [remark.pdf](https://alpo.ge/remark.pdf)
- The Wayback Machine availability API reports a capture of `remark.pdf` at timestamp 20261120141958 (14:19:58 UTC, 20 Nov 2026) and of `lean.tar.gz.part01` at 20261120142003; it reported these as the closest captures. — [Wayback availability API](https://archive.org/wayback/available?url=alpo.ge/remark.pdf); [capture URL](http://web.archive.org/web/20261120141958/https://alpo.ge/remark.pdf)
- Announced future edits: "probably I'll have to edit some of these descriptions on reflection." — [remark.pdf, p. 3 fn. 4](https://alpo.ge/remark.pdf)
- The Lean archive has no dates inside it (all mtimes zeroed); part ETags at 14:34–14:35 UTC were, e.g., part01 `"b116580303b65e25529dae6e694a3bab"`, part14 `"8a60f30a51ada38b89908f1ab8fcd86c"`; joined-archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (for later comparison). — [lean.tar.gz.part01](https://alpo.ge/lean.tar.gz.part01)
- The home page was not updated to mention the claim (fetched 14:34:10 UTC). — [alpo.ge](https://alpo.ge/)
- Scientific American describes its piece as "a breaking news story and will be updated" (via summarizing fetch tool). — [Scientific American, 20 Nov 2026](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)

### Inferences
- The statement was compiled at 12:52:48 UTC and was publicly reachable by 14:19:58 UTC at the latest; the exact posting time is not established by anything I could read.
- Since alpo.ge answers unknown paths with HTTP 200 and the home page, a future removal of `remark.pdf` or the Lean parts would show up as HTML being served at those URLs rather than as a 404; the hashes above allow later change detection.

### Gaps
- The Wayback capture itself and the Wayback CDX index could not be downloaded (repeated connection resets from web.archive.org), so I could not compare the 14:19:58 capture with the live file or check for earlier captures/versions.
- No server-side modification times are exposed for any of the files, so earlier silent replacements between 12:52 and 14:34 UTC cannot be ruled out from the headers alone.
- Whether the author has posted elsewhere (social media, mailing lists) with corrections or additions was outside the documents I could reach; none is linked from the statement or the home page.
