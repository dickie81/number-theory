# Lower bounds for $\lambda_{\min}(G_N)$

$Q(v)=v^TG_Nv=\sum_\rho|V(\rho)|^2/|\rho|^2$ (RH), $V(s)=\sum_{n\le N}v_nn^s$.

## Proved

**Theorem 1 (RH). $G_N\succ0$ for every $N$.**
Proof. Under RH, $Q\ge0$. If $Q(v)=0$ with $v\ne0$, then $D(s)=\sum_{n\le N}v_nn^{s}$ vanishes at every zero $\rho$, with multiplicity at least 1.
Let $n_1$ be the largest index with $v_{n_1}\ne0$. For $\sigma_0$ large (depending on $v$), $|D(\sigma_0+it)|\ge\tfrac12|v_{n_1}|n_1^{\sigma_0}$ uniformly in $t$, and $|D|\le\sum|v_n|n^{\sigma_0+R}$ on the disc of radius $R=\sigma_0+1$ about $\sigma_0+it_0$.
Jensen's formula then bounds the number of zeros of $D$ in each unit-height window of the strip $|\sigma-\tfrac12|\le1$ by a constant $C(v)$, uniformly in $t_0$. So $D$ has $O_v(T)$ zeros of height $\le T$. But $\zeta$ has $\sim\frac{T}{2\pi}\log T$ zeros on the critical line up to $T$ (all of them under RH; unconditionally Selberg gives $\gg T\log T$).
Contradiction. ∎ (So the minimum is never attained at finite N; this is the "nothing crosses" statement.)
The same argument without RH shows that the vectors $(n^\rho)_\rho$, $n\le N$, are linearly independent, i.e. $G_N$ (Hermitian, possibly indefinite) is nonsingular.

**Theorem 2 (RH). $\lambda_{\min}(G_N)\ll\log^2N/N$** (notes.md, Thm 6; test vector $(-1)^{n-1}/n$; cites a discrete mean-value theorem over zeros).

## Attempted: a lower bound $\gg\log N/N$ — not achieved

**(i) Density + fluctuation decomposition fails decisively.** Let $S_N$ be the Gram matrix with the zeros replaced by their density $\frac1{2\pi}\log\frac{|t|}{2\pi}$ on $|t|\ge2\pi$ (`smooth_eig.py`). Numerically:

| N | 25 | 50 | 100 | 200 |
|---|---|---|---|---|
| $\lambda_{\min}(S_N)$ | 5.047e-2 | 5.046e-2 | 5.046e-2 | 5.045e-2 |
| $\lambda_{\min}(G_N)$ | 6.79e-3 | 4.01e-3 | 2.35e-3 | 1.30e-3 |
| spec$(G_N-S_N)$ | [−1.0, 0.9] | [−4.0, 3.2] | [−15.8, 12.8] | [−62.7, 51.4] |

So the density model has **no horizon**: $\lambda_{\min}(S_N)\to\approx0.0505$, bounded below. The fluctuation $G-S$ (primes − density) has operator norm $\asymp N^2$ (it shifts the large-scale entries), far larger than either smallest eigenvalue. No Schur or Weyl perturbation bound can give $\lambda_{\min}(G)\gtrsim\lambda_{\min}(S)$: the near-null directions of $G$ are created by the arithmetic cancellation $\zeta(1-\rho)=0$ (formal kernel vectors $(1/n)*h$), which is invisible to the density. Any lower bound must handle the prime part non-perturbatively, i.e. with exact explicit-formula identities, not size estimates.

**(ii) Reverse mean value at zeros.** A bound $\sum_\rho|V(\rho)|^2/|\rho|^2\ge c\frac{\log N}{N}\|v\|^2$ amounts to a lower bound for the discrete mean value of a Dirichlet polynomial over the zeros. Gonek–Landau gives $\sum_{0<\gamma\le T}|V(\rho)|^2=\frac{T}{2\pi}\log\frac{T}{2\pi}\sum|v_n|^2n-\frac{T}{\pi}\mathrm{Re}\sum_{m}\sum_{n}v_mv_n\sqrt{mn}\,\Lambda(m/n)\cdots+E$, with $\Lambda(m/n)$ nonzero only when $m/n$ is a prime power. For our weight $1/|\rho|^2$ this is just the closed form of $G$ again. The error terms $E$ (Gonek: $O(N\log^2 \cdot)$ ) are of the same size as the main terms once $T\lesssim N$. The relevant zeros, those with $|\gamma|\lesssim N$, are exactly where the formula is not asymptotic. So I could not turn it into a lower bound. This is the same obstruction as in (i).

**(iii) Quantitative Jensen.** Making Theorem 1 quantitative (a lower bound for $\max_{\gamma\le T}|V(\rho)|$ in terms of $\|v\|$) gives at best something like $\lambda_{\min}\ge\exp(-C N^{A})$, through Turán-type power-sum bounds, and I have not carried out even that rigorously. **Open.**

## Literature
* **Connes–Consani(–Moscovici)** (arXiv:2106.01715, "Spectral triples and ζ-cycles"; "Zeta zeros and prolate wave operators", 2024; "Zeta spectral triples", arXiv:2511.22755). They restrict the Weil quadratic form to test functions supported on $[\lambda^{-1},\lambda]$. The smallest eigenvalues are extremely small, the eigenvectors are prolate-like, and the zeros of the Fourier transform of the bottom eigenvector approximate the low zeros of ζ. Their recent spectral-triple work assumes (and checks numerically) that the smallest eigenvalue $\epsilon_N$ of the finite restriction $QW_\lambda^N$ is simple with an even eigenvector.
  *Relation to $G_N$:* our $Q$ is the zero side of the Weil form evaluated on $\phi=(\sum_nv_n\sqrt n\,\delta_{\log n})*\tfrac12e^{-|u|/2}$, since the Fourier transform of $e^{-|u|/2}$ is $1/(\frac14+\gamma^2)$. Here $\sum_n v_n\sqrt n\,\delta_{\log n}$ is supported in $[0,\log N]$, which corresponds to $\lambda^2=N$ up to a translation, though the test functions are measures convolved with a fixed kernel rather than arbitrary $L^2$ functions on the interval. The two problems behave differently:
  - Their test space on a fixed interval is infinite-dimensional, so their $\epsilon$ is tiny and they study it at fixed $\lambda$.
  - Our space is the N point masses at $\log n$, and $\lambda_{\min}$ decays only like $\log N/N$.
  - They see zeros in the *eigenvector's* Fourier transform; we see formal kernel vectors whose Dirichlet series vanish at the zeros. Both say that near-null vectors of a restricted Weil form encode the zeros.
  I found no published lower bound for $\epsilon$ in their setting either. Positivity there (for all λ) is equivalent to RH, as for us.
* Burnol (2002) proves a lower bound $d_N^2\gg1/\log N$ for the Báez-Duarte distance. The structure there is rigid ($1-\zeta A$ equals 1 at the zeros), and the proof uses Hardy-space reproducing kernels. In our unrestricted orbit $\mathrm{dist}^2(w_1,\mathrm{span}\,w_{2..N})\approx N^{-0.87}$ (notes.md §4), so Burnol's method does not transfer directly. An adaptation would need the analogue of his "$1$ at the zeros" constraint, and our problem has none.
* Bombieri, "Remarks on Weil's quadratic functional" (2000): local positivity of the Weil functional for test functions supported in a small interval around 1. That is the analogue of $\lambda_{\min}>0$ for small N, with no rate.

## What remains
1. A lower bound $\lambda_{\min}(G_N)\gg N^{-A}$, for any A, under RH. Even $\exp(-N^{A})$ is not written down.
2. The conjectured order $\lambda_{\min}\asymp\log N/N$ (fit $\approx0.047\log N/N$; Theorem 2 gives the upper bound up to one log).
3. Any lower bound has to be non-perturbative in the primes (part (i)).
