# Tests of the orbit-lattice conjecture

This note collects analytic results, certified computations and counterexamples for the conjecture of
[ball-conjecture.md](ball-conjecture.md): the Gram–Schmidt pivots $d_k$ of the orbit with Gram matrix
$G(m,n)=\sqrt{mn}\,K_H(m/n)$, $K_H(r)=\sum_\rho r^{\rho-1/2}/(\rho(1-\rho))$, satisfy $d_k\ge d_1=K_H(1)=2+\gamma-\log4\pi$.
Scripts are in `scripts/ball_tests/` (see its README). Every claim below is labelled **Theorem** (proof given or sketched), **Certified** (ball arithmetic), **Numerical** (floating point) or **Conjecture**.
None of this is formalised in Lean.

## 1. The closed form of $K_H$

**Theorem A.** For $x\ge1$,
$$K_H(x)=\sqrt x\Big(\sum_{n\le x}\Lambda(n)\big(\tfrac1n-\tfrac1x\big)-\log x+1+\gamma-\frac{\log2\pi}{x}+t(1/x)\Big),\qquad t(y)=y+\tfrac12(1-y)\log(1-y)-\tfrac12(1+y)\log(1+y).$$
This is the formula of `scripts/ball_orbit.py`; `scripts/ball_certificate.py` records the same derivation.
*Proof.* Let $f(x)=\sum_\rho x^\rho/(\rho(1-\rho))$, which converges absolutely. Multiply the explicit formula $\psi_0(t)=t-\sum_\rho t^\rho/\rho-\log2\pi-\tfrac12\log(1-t^{-2})$ by $t^{-2}$ and integrate over $[1,x]$.
Termwise integration is justified by the bounded convergence of the symmetric partial sums on compact sets (Davenport, ch. 17). Since $\int_1^xt^{\rho-2}dt/\rho=(1-x^{\rho-1})/(\rho(1-\rho))$, we get $f(x)/x=f(1)+\int_1^x(\psi_0(t)-t+\log2\pi+\tfrac12\log(1-t^{-2}))t^{-2}dt$. The remaining integrals are elementary, and $K_H(x)=f(x)/\sqrt x$. ∎

**Dirichlet analogue (Theorem A′).** Let $\chi$ be primitive mod $q$ with parity $a$, and $K_\chi(x)=\sum_\rho x^{\rho-1/2}/(\rho(1-\rho))$. The same argument with Davenport ch. 19 gives, for $x\ge1$ and $y=1/x$,
$K_\chi(x)=\sqrt x\,[K_1+\sum_{n\le x}\chi(n)\Lambda(n)(\frac1n-\frac1x)+(1-a)(1-\frac{1+\log x}{x})+b(1-\frac1x)-C_a+t_a(y)]$, where:
- $K_1=\log\frac q\pi+\psi(\frac{1+a}2)+2\,\mathrm{Re}\,\ell$, with $\ell=L'/L(1,\chi)$;
- $b=-\log\frac q\pi+\gamma+\log2-\bar\ell$;
- $C_0=1-\log2$ and $t_0=t$;
- $C_1=\log2$ and $t_1(y)=y\,\mathrm{artanh}\,y+\frac12\log(1-y^2)$.

Checked against direct sums over zeros (|γ| < 60) for four characters, to the truncation error (`dirichlet/validate.py`).

## 2. The case $k=2$

$G_{11}=K_1$, $G_{22}=2K_1$ and $G_{12}=\sqrt2K(2)$, so $d_2/d_1=2(1-|K(2)|^2/K_1^2)$. At $x=2$ the prime sum in Theorem A′ vanishes.

**Theorem B.** $K(2)=\sqrt2(\tfrac12K_1+c_a+\tfrac12\ell)$. Hence
$$d_2\ge d_1\iff|K_1+2c_a+\ell|\le K_1,\qquad c_0=-\tfrac14\log\tfrac{27}{4}=-0.4773856262\ldots,\ c_1=\tfrac34\log\tfrac34=-0.2157615543\ldots$$
(The constant $\gamma$ cancels from $c_a$, and what is left is a log of a rational; Lean: `D2Criterion.c0_closed`, `c1_closed`, `CAClosed.cA_zero`, `CAClosed.cA_one`.) For real $\chi$ this says $-2K_1-2c_a\le\ell\le-2c_a$. In particular it requires $L'/L(1,\chi)\le\tfrac12\log\tfrac{27}{4}=0.95477$ (even $\chi$) and $\le\tfrac32\log\tfrac43=0.43152$ (odd $\chi$). The density of real characters that fail is in [d2-density.md](d2-density.md).

**Certified (arb).** For $\zeta$: $d_2/d_1=1.71841346690985319155\ldots$

## 3. Certified pivots for ζ

**Certified (cross-check).** `scripts/ball_certificate.py` already proves $d_k>d_1$ for $2\le k\le10^4$ ([ball-conjecture.md](ball-conjecture.md), step 6), with every rounding bounded. Independently, ball arithmetic at 256 bits on the closed form of Theorem A gives $d_k/d_1>1$ for all $2\le k\le500$ (`hunt/cert_zeta.py`, output `cert500.txt`). The minimum is at $k=2$. Selected values: $d_{10}/d_1=6.3508269$, $d_{100}/d_1=35.672522$, $d_{500}/d_1=74.930553$.
Since Theorem A is unconditional, this is a statement about the matrix defined by the zero sum and does not assume RH.
**Numerical.** A dps-40 rerun of `ball_orbit.py` agrees with its float64 pivots to relative error $9.7\times10^{-12}$ for $N\le500$.

## 4. Function fields

**Definition.** Let $C/\mathbb F_q$ have genus $g$ and $L$-polynomial $\prod_j(1-\alpha_jT)$, with $\alpha_j=\sqrt q\,e^{i\theta_j}$. The zeros of $\zeta_C(s)$ are $\frac12+i(\theta_j+2\pi k)/\log q$ for $k\in\mathbb Z$. Define $K(r)=\sum_\rho r^{\rho-1/2}/(\rho(1-\rho))$ and $G(m,n)=\sqrt{mn}\,K(m/n)$ for $m,n\ge1$, exactly as for ζ. Poisson summation gives
$K(r)=\log q\sum_{m\in\mathbb Z}s_mq^{-m/2}e^{-|\log r-m\log q|/2}$, where $s_m=\sum_j\alpha_j^m$ and $s_{-m}=q^{-m}s_m$. Every entry is a rational multiple of $\log q$.
The $m=0$ term alone is $2g\log q\cdot\min(m,n)$, which is the flat model. $G$ is positive semidefinite because the weights $1/(\frac14+\gamma^2)$ are positive.
(The doc's own analogue, the orbit of Frobenius powers $\Gamma_k$, has a Toeplitz Gram matrix of rank $\le2g$, so $d_k=0$ for $k>2g$.)

**Theorem C.** $d_k=0$ at $k=q^{2g}$, and already at $k=q$ if all $\alpha_j$ are equal. So the conjecture fails for every curve once $N\ge q^{2g}$.
*Proof.* $q^{i\gamma}=e^{i\theta_j}$ depends only on $j$. Hence $w_{nq^a}=q^{a/2}\sum_je^{ia\theta_j}P_jw_n$, where $P_j$ projects onto the zeros in class $j$. So the $2g+1$ vectors $w_{q^a}$ ($0\le a\le2g$) lie in a space of dimension $2g$. ∎

**Numerical.** 148 curves: genus 1–3, $q\in\{2,3,4,5,7,9,11,13\}$, smooth hyperelliptic models plus the extremal $L$-polynomials that curves have (the maximal and minimal elliptic curves over $\mathbb F_4$ and $\mathbb F_9$, and the Hermitian quartic over $\mathbb F_9$), $k\le150$. 98 of them have some $d_k<d_1$, 43 first at $k=2$ (e.g. $q=3$, $g=2$, $L=1-T-2T^2-3T^3+9T^4$, $d_2/d_1=0.526$). The minimal elliptic curve over $\mathbb F_4$ has $d_2/d_1=2/9$ and $d_3/d_1=1/6$. Restricting to indices $q\nmid n$ removes the forced zeros, but 59 of 148 curves still fail. Exact ties $d_k=d_1$ are not counted as failures.

## 5. Dirichlet L-functions: counterexamples

**Certified + verified.** Values come from arb on Theorem B and are cross-checked by direct sums over zeros found with flint's Hardy $Z$:
* $\chi$ mod 19, Conrey label 3 (odd, zero at $\gamma\approx-0.019$): $K_1=4.3578$, $|K(2)|/K_1=0.8915$, $d_2/d_1=0.4105$.
* $\chi_{-163}$ (real, odd, zeros at $\pm0.2029$): $\ell=2.168>0.4315$, $d_2/d_1=0.4986$.
* $d_2<d_1$ for 5983 of the 29468 primitive characters with $q\le400$, and for 637 of the 6086 real primitive characters with $q\le10^4$.

So $d_k\ge d_1$ is **not** a consequence of GRH or of Weil positivity. The failures go with large $K_1$ (a low zero, or $L'/L(1,\chi)$ large). Heuristically: the density of zeros alone gives the flat model $c\min(m,n)$, whose pivots all equal $d_1$, and fluctuations push the pivots to either side.
**Suggested restatement (Conjecture).** The margin $d_k\ge d_1$ is specific to ζ (conductor 1, $K_1=0.046$, first zero at 14.13). A version for general $L$ would have to subtract the flat-model contribution, for example $d_k\ge d_1-\epsilon(K_1)$, or apply only when the conductor and the first zero satisfy explicit inequalities. §5.1 shows that, in the range scanned, the first two or three pivots already decide it. (The `dirichlet/` sample, $q\le47$, happens to contain no failure; the pair mod 13 with Conrey labels 6 and 11, $K_1=1.28$, fails at $k=3$.)

### 5.1 Where the failures occur

Write $B_{mn}=K(m/n)/K_1$ for the cosines between the orbit vectors. Then $d_k/d_1=k\det B_k/\det B_{k-1}$. So $d_k\ge d_1$ says that the $k$-th unit orbit vector has squared distance at least $1/k$ from the span of the earlier ones.

**Theorem B′ ($k=3$).** Let $\lambda=\ell/K_1$ and $\kappa=1/K_1$. By Theorem A′, $S(2)=S(3/2)=0$ and $S(3)=\chi(2)\log2/6$, so the cosines $u=K(2)/K_1$, $v=K(3)/K_1$, $w=K(3/2)/K_1$ are affine in $\lambda$ and $\kappa$:
$$u=\tfrac{1}{\sqrt2}(1+\lambda+2c_a\kappa),\qquad w=\tfrac{1}{\sqrt6}(2+\lambda+3e_a\kappa),\qquad v=\tfrac{1}{\sqrt3}\big(1+2\lambda+(\tfrac12\chi(2)\log2+3f_a)\kappa\big),$$
$$\frac{d_3}{d_1}=\frac{3\,(1-|u|^2-|v|^2-|w|^2+2\,\mathrm{Re}(uw\bar v))}{1-|u|^2}.$$
Here $e_0=-\tfrac16\log\tfrac{3125}{256}=-0.4170020196$, $e_1=\tfrac16\log\tfrac{3125}{11664}=-0.2195121487$, $f_0=-\tfrac23\log2$ and $f_1=\tfrac13\log\tfrac{16}{27}=-0.1744160479$, with $c_a$ as in Theorem B. As for $c_a$, $\gamma$ cancels and evaluating Theorem A′ at $x=3/2$ and $3$ leaves these logs of rationals. At $\lambda=\kappa=0$ these are the cosines $\min(m,n)/\sqrt{mn}$ of the flat model, whose pivots all equal $d_1$.
More generally, $G_k$ depends only on $K_1$, $\ell$, the parity and $\chi(p)$ for primes $p<k$.

**Corollary (real $\chi$).** For real $\chi$, Theorem A′ gives $\ell=\tfrac12(K_1-\log\frac q\pi-\psi(\frac{1+a}2))$. With $L_a=\log\frac q\pi+\psi(\frac{1+a}2)-4c_a$, that is $\log\frac q\pi-0.0540$ (even) or $\log\frac q\pi+0.2858$ (odd), Theorem B becomes
$$d_2\ge d_1\iff \tfrac15L_a\le K_1\le L_a .$$
The upper end is $\ell\le-2c_a$. Since $2\ell=K_1-(\log\frac q\pi+\psi(\frac{1+a}2))$ is the excess of $\sum_\rho1/|\rho|^2$ over what the zeros' density gives, $d_2<d_1$ means the low zeros carry too much weight.

**Certified + numerical (`hunt/kmin.py`).** For each primitive character, $d_k/d_1$ is certified for $k\le8$ by an LDL in arb of the closed-form $G_8$. It agrees with the $k\le3$ formula to $10^{-15}$. Beyond that, float64 pivots up to $k=300$ from the same closed form are checked against `dirichlet/dcore.py` to $3\times10^{-13}$.
* *All primitive $\chi$, $q\le400$ (29468 characters; `kmin_all400.txt`).*
  * 5983 have $d_2<d_1$ and 4 more have $d_3<d_1\le d_2$: the pairs mod 13 (labels 6, 11) and mod 61 (labels 6, 51), all odd and complex. No other character has a certified failure for $k\le8$.
  * The remaining 23481 have $d_k\ge d_1$ for every $k\le300$. Their smallest margin, $5.7\times10^{-5}$ (mod 361, label 5, at $k=2$), is far above the float error.
  * The minimum over $k$ sits at $k=2$ for 29378 characters, at $k=3$ for 69, at $k=4$ for 19 and at $k=5$ for 2. Of these, three passing characters have their minimum at $k=4$: mod 19 label 18 ($d_4/d_1=1.626$), and the pair mod 59 (labels 18, 23) with $d_4/d_1=1.0034$, a near miss.
* *Real primitive $\chi$, $q\le10^4$ (6086 characters; `kmin_real10000.txt`).*
  * All 637 failures occur at $k=2$, and every one is at the upper end: they are exactly the characters with $\ell>-2c_a$ (0.9548 even, 0.4315 odd). The other 5449 have $d_k\ge d_1$ for every $k\le300$.
  * An independent computation of $\ell_D$ with PARI gives the same counts: 153 of 3043 even and 484 of 3043 odd ([d2-density.md](d2-density.md), `scripts/d2_density/lower.py`).
  * The failure rate by $q$ range ($<10^3$, $10^3$–$3\cdot10^3$, $3\cdot10^3$–$6\cdot10^3$, $6\cdot10^3$–$10^4$) is 2.3%, 4.4%, 5.5%, 5.7% for even $\chi$ and 10.2%, 15.5%, 17.0%, 16.7% for odd $\chi$.

**Reading.** In the range scanned, the conjecture for a Dirichlet $L$-function is decided by its first pivots:
- for real characters by $k=2$, that is by the size of $L'/L(1,\chi)$;
- for every character with $q\le400$ by $k\le3$.

The mod-59 near miss at $k=4$ means $k\le3$ should not be expected to decide in general. A bounded $k$ might.

The real failure rate settles at a positive proportion, because $L'/L(1,\chi_D)$ has a limiting distribution over fundamental discriminants (Mourtada–Murty; Lamzouri's random model). [d2-density.md](d2-density.md) proves the per-sign limits.
- The proportion of $D\gtrless0$ with $d_2<d_1$ tends to $P(X>\tfrac12\log\tfrac{27}4)=0.0511$ and $P(X>\tfrac32\log\tfrac43)=0.1609$. The average is $0.106$, a model value that is not certified.
- The proof is written out unconditionally there. The Lean version is conditional on the zero-free half-plane input.
- Its data run to $|D|\sim10^8$. The rates above rise with $q$ and already overshoot these limits at $6\cdot10^3$–$10^4$.
- That note traces the overshoot to a finite-$D$ transient: the spread and the skewness of $\ell_D$ converge at different speeds. The excess peaks near $10^5$ and is gone by $10^6$.

## 6. The horizon: smallest eigenvalues

**Theorem D (zero-sum form).** Unconditionally, $v^TG_Nv=\sum_\rho V(\rho)V(1-\rho)/(\rho(1-\rho))$, where $V(s)=\sum_{n\le N}v_nn^s$. Under RH this is $\sum_\rho|V(\rho)|^2/|\rho|^2$.

**Theorem E (RH). $G_N\succ0$ for every $N$.** If $Q(v)=0$ then $D(s)=\sum v_nn^s$ vanishes at every zero. By Jensen's formula, in discs centred where the largest-index term dominates, $D$ has $O_v(1)$ zeros per unit of height, while ζ has $\sim\frac T{2\pi}\log T$ zeros up to height $T$. ∎ The argument needs RH: without it the form pairs $\rho$ with $1-\bar\rho$ and is indefinite, so $Q(v)=0$, or even $G_Nv=0$, does not force $V(\rho)=0$, and independence of the $(n^\rho)_\rho$ does not give nonsingularity. Unconditionally $G_N\succ0$ is known only for $N\le10^4$ (§3).

**Theorem F (RH). $\lambda_{\min}(G_N)\ll\log^2N/N$.** Take $v_n=(-1)^{n-1}/n$. Then $V(\rho)=\eta(1-\rho)-\text{tail}$, and $\eta(1-\rho)=0$. The tail is $\pm\frac12N^{\rho-1}+O(|\rho|N^{-3/2})$ for $|\gamma|\le N$. For $|\gamma|>N$ we use a discrete mean-value theorem for Dirichlet polynomials over the zeros (large-sieve type, $\ll(T+N)\log T\sum|a_n|^2$ per dyadic block). That step is cited and its constants are not computed. **Numerical:** this vector's Rayleigh quotient is about $0.15\log N/N$, and $\lambda_{\min}$ is about 0.31 times it.

**Certified.** $\lambda_{\min}(G_N)$ at $N=100,300,1000$ is $2.3448094\times10^{-3}$, $9.3070857\times10^{-4}$ and $3.3178750\times10^{-4}$. Each is certified to relative $10^{-6}$ (or $10^{-5}$ at $N=1000$) by Sylvester inertia in arb (`horizon/cert_inertia.py`).
**Numerical / Conjecture.** $\lambda_{\min}\approx c\,(\log N)^{0.885}/N$ with $c\approx0.06$; equivalently $\lambda_{\min}N/\log N=0.051,0.048,0.047$ at $N=100,1000,3000$. **Conjecture:** $\lambda_{\min}\asymp\log N/N$. No lower bound of any power-type is proved.
**Obstruction (Numerical).** With the zeros replaced by their density, $\lambda_{\min}$ stays at about 0.0505 for $N\le200$: the density model has no horizon. Meanwhile $G-S$ has operator norm about $N^2/620$ (62.7 at $N=200$). So no perturbative (Schur or Weyl) argument can give a lower bound; the near-null directions come from the exact identity $\zeta(1-\rho)=0$.

**Eigenvectors.**
* *Flat-model pencil* $G v=\lambda d_1\min(m,n)v$: $\lambda_{\min}\approx1.29\,N^{-1.97}\log^{0.75}N$ (fitted; $e^{0.2568}=1.29$). The eigenvector is $\approx1/n$ ($nv_n=1.00$–$1.08$) plus an edge layer at $n\approx N$. **Theorem (elementary).** In difference variables $u_k=\sum_{n\ge k}v_n$, the vector $v=1/n$ gives $u_k\approx\log(N/k)$, so dyadic block $j$ carries weight $\propto2^j(\log_2N-j)^2$, which peaks at $\log_2N-j=2/\ln2\approx2.89$. This matches the observed "traveling wave" (at $N=6000$, predicted and measured block weights agree to about 0.01). Also $Q(1/n)=NS_4(1+o(1))$ with $S_4=\sum|\rho|^{-4}=7.4198\times10^{-5}$ (Euler–Maclaurin plus $\zeta(1-\rho)=0$); numerically, Rayleigh$/N$ is $4.5130\times10^{-5}$ against $S_4/\zeta(2)=4.5107\times10^{-5}$.
* *Euclidean problem.* The bottom eigenvector freezes (97.5% of its weight on $n<16$, overlap 0.998 between $N=100$ and $6000$). $f(n)=nv_n$ is multiplicative to within 0.3% on average, with $f(p)\approx p/(p+1)$ for small $p$; for example $f(2)=0.669$ and $f(2^k)\to\approx0.60$ at $N=8000$. It drifts by about $-0.004$ per doubling of $N$, so the limit is not determined. **Theorem (correction).** The natural variational problem (minimise $\|v\|$ over formal kernel vectors $v=(1/n)*h$, i.e. $\sum v_nn^{-z}=\zeta(1+z)H(z)$, with $v_1=1$) is degenerate: the infimum is 1 and is not attained. Take $H_y=\prod_{p\le y}(1-p^{-1-z})$; the limit is $e_1$, which is not a kernel vector. So the limit is selected at order $\log N/N$ by the boundary cost, and has no closed form yet.
* *Contrast.* The curve over $\mathbb F_{13}$ with $L=1+2T+13T^2$ has an exact null vector on $\{1,13,169\}$ from $N=169$ on (Theorem C); for ζ, by Theorem E, no finite $N$ has one.

## 7. Literature
* A. Weil, *Sur les "formules explicites" de la théorie des nombres premiers* (1952); positivity criterion.
* E. Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers I*, Rend. Mat. Acc. Lincei (2000).
* J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Adv. Math. 170 (2002); arXiv:math/0103058. Note $d_1=\sum_\rho1/|\rho|^2$ is Burnol's constant when the zeros are simple. The unrestricted orbit does **not** inherit his $1/\log N$ bound: numerically $\mathrm{dist}^2(w_1,\mathrm{span}\,w_{2..N})\approx N^{-0.87}$.
* L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Rend. Mat. Acc. Lincei (2003); arXiv:math/0202141.
* J. B. Conrey, X.-J. Li, *A note on some positivity conditions related to zeta and L-functions*, IMRN 2000: de Branges' positivity condition fails, a precedent for strengthenings of Weil positivity failing.
* A. Connes, C. Consani, *Spectral triples and ζ-cycles*, arXiv:2106.01715; Connes, Consani, Moscovici, *Zeta zeros and prolate wave operators*, Ann. Funct. Anal. (2024); Connes, Consani, Moscovici, *Zeta spectral triples*, arXiv:2511.22755. They study the Weil form restricted to $[\lambda^{-1},\lambda]$, whose small eigenvalues have prolate-like eigenvectors that encode low zeros. Our $Q$ is the zero side of the Weil form on $\sum v_n\sqrt n\,\delta_{\log n}$ convolved with $\frac12e^{-|u|/2}$, supported in $[0,\log N]$ ($\lambda^2=N$). Their test space is infinite-dimensional, so their eigenvalue is tiny; ours decays only like $\log N/N$.
* H. Davenport, *Multiplicative Number Theory*, ch. 17 and 19 (explicit formulae).

## Open
* A lower bound for $\lambda_{\min}(G_N)$ under RH, even $\exp(-N^A)$.
* $d_k\ge d_1$ for ζ for all $k$, even assuming RH; and a version of the conjecture that survives §4–5.
* The limiting Euclidean eigenvector, and the effective functional that selects it.
* Whether a bounded number of pivots decides $d_k\ge d_1$ for every Dirichlet $L$-function (§5.1). For real characters, whether $d_2$ alone decides it beyond $q\le10^4$; if so, [d2-density.md](d2-density.md) gives the density of failures of the whole conjecture.

*Prepared with AI assistance (Grok Bot). Certified numbers rest on python-flint/arb ball arithmetic; everything marked Numerical is floating point.*
