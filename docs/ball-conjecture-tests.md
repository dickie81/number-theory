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
(The doc's own analogue, the orbit of Frobenius powers $\Gamma_k$, has a Toeplitz Gram matrix of rank $\le2g$, so $d_k=0$ for $k>2g$. This is the Gram matrix of E. Hallouin and M. Perret, Trans. AMS 372 (2019), Lemma 3: $2gq^k$ on the diagonal and $q^{\min(i,k)}s_{|i-k|}$ off it, with Weil's bound a $2\times2$ Gram determinant and Ihara's a $3\times3$ one. Its $2\times2$ case gives $d_2\ge d_1\iff|q+1-\#C(\mathbb F_q)|\le2g\sqrt{q-1}$, which maximal curves violate.)

**Theorem C.** $d_k=0$ at $k=q^{2g}$, and already at $k=q$ if all $\alpha_j$ are equal. So the conjecture fails for every curve once $N\ge q^{2g}$.
*Proof.* $q^{i\gamma}=e^{i\theta_j}$ depends only on $j$. Hence $w_{nq^a}=q^{a/2}\sum_je^{ia\theta_j}P_jw_n$, where $P_j$ projects onto the zeros in class $j$. So the $2g+1$ vectors $w_{q^a}$ ($0\le a\le2g$) lie in a space of dimension $2g$. ∎

**Theorem C′ (the null vector is integral).** Let $m(z)=\sum_{k\le d}m_kz^{d-k}$ be the minimal polynomial of Frobenius: the squarefree part of $L^*(z)=z^{2g}L(1/z)=\prod_j(z-\alpha_j)$, monic with integer coefficients, of degree $d\le2g$ ($d=2g$ when the $\alpha_j$ are distinct, $d=1$ when they are all equal). Then $\sum_km_kw_{q^{d-k}}=0$. So $d_k=0$ already at $k=q^d$, and the integer vector with entry $m_k$ at $n=q^{d-k}$ has $Q=0$: the shortest-vector form fails for every curve at $N=q^d$ (§7).
*Proof.* By the proof of Theorem C, $w_{q^a}=\sum_j\alpha_j^aP_jw_1$, so $\sum_km_kw_{q^{d-k}}=\sum_jm(\alpha_j)P_jw_1=0$. ∎
Checked in exact rational arithmetic for all 148 curves below (`shortest/shortest.py`; $G$ is $\log q$ times a rational matrix).

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

## 7. The shortest-vector form

The conjecture has a second form, which asks less. Call the pivot form (A). The shortest-vector form (B) asks that $Q_N(a)\ge d_1=Q(\delta_1)$ for every nonzero integer vector $a$ and every $N$, that is, that $w_1$ be a shortest vector of the lattice the orbit spans. For ζ, (B) is equivalent to RH (`PivotSharp.rh_iff_shortest`), as (A) is (`PivotSharp.rh_iff_orbitLattice`). Under RH every integer vector other than $\pm\delta_1$ has $Q\ge0.0577=1.249\,d_1$ (`PivotSharp.lattice_gap`). Write $s_2$ for the second minimum, the least $Q(a)/d_1$ over integer $a\ne0,\pm\delta_1$. (B) fails exactly when $s_2<1$. In the flat model every increment $\delta_n-\delta_{n-1}$ has $Q=d_1$, so there $s_2=1$. Script: `shortest/shortest.py`, output `out.txt`.

**Theorem G.**
1. *(B) is weaker than (A).* If $a_k$ is the last nonzero entry of an integer vector $a$, then $Q(a)\ge a_k^2d_k\ge d_k$. So (A) for $k\le N$ gives (B) at $N$, and a failure of (B) at a vector ending at $k$ is a failure of (A) at $k$.
2. *Integer vectors see only $\mathrm{Re}\,G$:* $Q(a)=a^T(\mathrm{Re}\,G)a$. For a real Gram matrix this changes nothing. For a complex character, $G_{\bar\chi}=\overline{G_\chi}$, so $\mathrm{Re}\,G=\frac12(G_\chi+G_{\bar\chi})$: half the Gram matrix of the same construction over the zeros of $L(s,\chi)L(s,\bar\chi)$. Its pivots are minima over real coefficients only, so they are at least those of $G$.
3. *At $k=2$ the two forms coincide.* Every orbit Gram matrix has $G_{22}=2G_{11}=2d_1$. Write $g=\mathrm{Re}\,G_{12}/d_1$. Then $Q(a\delta_1+b\delta_2)=d_1\big((a+bg)^2+b^2(2-g^2)\big)$, so (B) holds at $N=2$ exactly when $|g|\le1$. Otherwise $\delta_2-\mathrm{sgn}(g)\delta_1$ has $Q=(3-2|g|)d_1<d_1$. And $d_2(\mathrm{Re}\,G)=(2-g^2)d_1$, so this is (A) at $k=2$ for $\mathrm{Re}\,G$. For a character, Theorem B gives $\mathrm{Re}\,G_{12}=K_1+2c_a+\mathrm{Re}\,\ell$, and with $K_1=\log\frac q\pi+\psi(\frac{1+a}2)+2\,\mathrm{Re}\,\ell$:
$$\text{(B) holds at }N=2\iff\tfrac15L_a\le K_1\le L_a,$$
the criterion of the Corollary in §5.1, now for every $\chi$, real or complex. It depends only on the zero sum $K_1$. (A) at $k=2$ for $G$, $|K_1+2c_a+\ell|\le K_1$, also involves $\mathrm{Im}\,\ell$.
4. *Curves.* (B) fails for every curve at $N=q^d$ (Theorem C′).
5. *The Frobenius orbit.* Its integer span is the lattice $\mathbb Z[z]/(m)$, with basis $1,z,\dots,z^{d-1}$, although the orbit vectors are dependent: the dependencies are integral, since $m$ is monic. The form $T(P)=\sum_j|P(\alpha_j)|^2$ has the integral Gram matrix $q^{\min(i,j)}s_{|i-j|}$ and $T(1)=2g$. If $m$ is irreducible, then $L^*=m^e$ and $\prod_jP(\alpha_j)=\mathrm{Res}(m,P)^e$ is a nonzero integer for $P\notin(m)$. AM–GM then gives $T(P)\ge2g$, so (B) holds. Equality at some $P\ne\pm1$ forces $|P(\alpha_j)|=1$ for every $j$, so by Kronecker's theorem $P(\alpha)$ is a root of unity in $\mathbb Z[\alpha]$ other than $\pm1$. An example is the curve over $\mathbb F_2$ with $L=1-2T+2T^2$, where $\alpha=1+i$ and $P=z-1$ gives $P(\alpha)=i$. (A) fails for every curve, at $z^d$, whose pivot is $0$.

**Results.** The searches are Fincke–Pohst enumerations in float64, up to $1.5\,d_1$ ($3\,d_1$ for ζ). Every failure is certified: in exact rational arithmetic for curves and in arb for characters. Passes are numerical, with the margins shown.

| Analogue | Cases | Indices | (A) fails | (B) fails | (B) fails only beyond the first two indices | Least $s_2$ where (B) holds |
|---|---|---|---|---|---|---|
| ζ | 1 | $n\le30$ | 0 | 0 | 0 | 1.9387 (at $\delta_1+\delta_2$; arb $1.93870544505279\ldots$) |
| curves, $n<q^d$ | 148 | $n\le\min(20,q^d-1)$ | 59, 43 of them at $k=2$ | 43 | 0 | 1 (exact ties, 18 curves) |
| curves, $q\nmid n$ | 148 | first 20 | 53, 39 at the second index | 39 | 0 | 1 (exact ties, 15 curves) |
| curves, $n\le q^d$ | 148 | | all, at $q^d$ | all, at $q^d$ (Theorem C′, exact) | | |
| Frobenius orbit, $\mathbb Z[z]/(m)$ | 148 | all | all, at $z^d$; 1 earlier | 0 | 0 | 1 (exact ties, 4 curves) |
| primitive χ, $q\le400$ | 29468 (242 real) | $n\le12$ | 5987 for $G$, 5983 of them at $k=2$; 5443 for $\mathrm{Re}\,G$, all at $k=2$ | 5443 | 0 | 1.000037 (mod 311, label 232) |
| real primitive χ, $q\le10^4$ | 6086 | $n\le12$ | 637, all at $k=2$ | 637 | 0 | 1.0010 (mod 9867) |

Notes on the table:
- For curves, $d$ is the degree of the minimal polynomial of Frobenius, and $q^d$ runs from 4 to $13^6=4826809$ (median 256). For 28 of the 148 curves, $q^d\le20$.
- In the second row, 16 curves fail (A) in the window and pass (B) there. In the third, 14 do.
- The one enumeration that hit its node budget is the minimal elliptic curve over $\mathbb F_4$ with $q\nmid n$, which fails (B) at the first two indices anyway ($d_2/d_1=2/9$).
- In the Frobenius row, $m$ is irreducible for 132 curves, where (B) holds by item 5, and reducible for 16, where the search finds no failure.
- Every failure of (B) among the characters is at $\delta_2-\delta_1$, at the upper end $K_1>L_a$ of item 3. The worst is χ mod 19 with Conrey label 3, at $Q=0.479\,d_1$; among real characters it is $\chi_{-163}$, at $0.549\,d_1$.
- Of the 29226 complex characters with $q\le400$, 5974 fail (A) for $G$ at $k=2$ and 5434 fail (B), all at $N=2$. The other 540 fail (A) only through $\mathrm{Im}\,\ell$, and pass (B).
- The four characters of §5.1 that first fail (A) at $k=3$ (mod 13, labels 6 and 11; mod 61, labels 6 and 51) pass (B) and (A) for $\mathrm{Re}\,G$, with $s_2=1.337$ and $1.100$.
- Near misses: 201 passing characters with $q\le400$, and 27 real ones with $q\le10^4$, have $s_2<1.01$. The closest, χ mod 311 with label 232, has $s_2=1.000037$, a margin far above the float error, and its decision at $N=2$ is certified in arb.

**Reading.** On every analogue built by the same formula as for ζ, (B) failed exactly where $d_2(\mathrm{Re}\,G)<d_1$, at $N=2$, where by item 3 it is (A). For a real Gram matrix that is $d_2<d_1$. The one exception is the forced null vector at $N=q^d$ for curves. (A) fails where (B) holds in three cases: for 16 curves, beyond $k=2$; for the four characters of §5.1 that fail at $k=3$; and for 540 complex characters at $k=2$, through $\mathrm{Im}\,\ell$. So (B) is weaker than (A) but fails on the same analogues: for every curve, and for a positive proportion of real characters. Every real character with $d_2<d_1$ fails (B) at $N=2$, so the positive proportion of [d2-density.md](d2-density.md) fails (B) too. In the range scanned these are all the failures. The two forms part only on the Frobenius orbit. There (A) fails for every curve, because the orbit vectors are dependent, while (B) holds for the whole sample, by integrality whenever $m$ is irreducible. The integral dependencies that make the Frobenius orbit a lattice are what (B) sees and (A) does not. For ζ, $s_2=1.939$ on $n\le30$, against $1.249$ from the Lean proof under RH.

## 8. Literature
* A. Weil, *Sur les "formules explicites" de la théorie des nombres premiers* (1952); positivity criterion.
* E. Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers I*, Rend. Mat. Acc. Lincei (2000).
* J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Adv. Math. 170 (2002); arXiv:math/0103058. Note $d_1=\sum_\rho1/|\rho|^2$ is Burnol's constant when the zeros are simple. The unrestricted orbit does **not** inherit his $1/\log N$ bound: numerically $\mathrm{dist}^2(w_1,\mathrm{span}\,w_{2..N})\approx N^{-0.87}$.
* L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Rend. Mat. Acc. Lincei (2003); arXiv:math/0202141.
* J. B. Conrey, X.-J. Li, *A note on some positivity conditions related to zeta and L-functions*, IMRN 2000: de Branges' positivity condition fails, a precedent for strengthenings of Weil positivity failing.
* A. Connes, C. Consani, *Spectral triples and ζ-cycles*, arXiv:2106.01715; Connes, Consani, Moscovici, *Zeta zeros and prolate wave operators*, Ann. Funct. Anal. (2024); Connes, Consani, Moscovici, *Zeta spectral triples*, arXiv:2511.22755. They study the Weil form restricted to $[\lambda^{-1},\lambda]$, whose small eigenvalues have prolate-like eigenvectors that encode low zeros. Our $Q$ is the zero side of the Weil form on $\sum v_n\sqrt n\,\delta_{\log n}$ convolved with $\frac12e^{-|u|/2}$, supported in $[0,\log N]$ ($\lambda^2=N$). Their test space is infinite-dimensional, so their eigenvalue is tiny; ours decays only like $\log N/N$.
* K. Matsumoto, M. Suzuki, *M-functions and screw functions: applications to Goldbach's problem and zeros of the Riemann zeta-function*, J. Number Theory 280 (2026), 918–946; arXiv:2409.00888. Their $H_1$ is $K_H$, and their Theorem 1.3 says that RH holds exactly when $H_1(e^t)-H_1(1)$ is a screw function. $G_N\succeq0$ for every $N$ is a discrete form of it.
* J.-L. Nicolas, *Small values of the Euler function and the Riemann hypothesis*, Acta Arith. 155 (2012), 311–321; arXiv:1202.0729. His $\beta=\sum_\rho1/(\rho(1-\rho))=2+\gamma-\log4\pi$ is $d_1$, and under RH $|W(x)|\le\beta$ with $W=K_H$: the $2\times2$ minors of $G_N$.
* J.-F. Burnol, arXiv:math/9810169 (1998), and S. Gun, M. R. Murty, P. Rath, Mathematika 64 (2018): RH holds exactly when $\sum_\rho1/|\rho|^2=2+\gamma-\log4\pi$, that is, $d_1=\sum_\rho1/|\rho|^2$.
* J. C. Lagarias, *Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007), Theorem 3.1: the Gram matrix $\lambda_n+\lambda_{-m}-\lambda_{n-m}$ of Weil's scalar product on Li's functions. It is the same pairing on another orbit of $1/s$, the powers of $1-1/s$, and under RH its pivots fall to $0$: $0.0462$, $7.4\cdot10^{-5}$, …, $5.9\cdot10^{-23}$ at $k=8$ (`prior_art/li_orbit.py`).
* D. S. Lubinsky, J. Approx. Theory 177 (2014), and D. K. Dimitrov, W. D. Oliveira, arXiv:1608.07887, §2.3: Dirichlet polynomials orthogonal for the arctangent density $dt/(2\pi(\frac14+t^2))$, which is the flat model $\min(m,n)$.
* E. Hallouin, M. Perret, *A unified viewpoint for upper bounds for the number of points of curves over finite fields via Euclidean geometry and semi-definite symmetric Toeplitz matrices*, Trans. AMS 372 (2019), 5409–5451: the Gram matrix of the Frobenius orbit (§4, §7).
* H. Yoshida, *On Hermitian forms attached to zeta functions*, Adv. Stud. Pure Math. 21 (1992), 281–325: Weil's form on windows, non-degenerate there, with explicit lower bounds for squared norms; no pivots.
* The literature check behind these entries, which found no statement of the conjecture in either form: [reports/Orbit lattice criterion prior art.md](../reports/Orbit%20lattice%20criterion%20prior%20art.md).
* H. Davenport, *Multiplicative Number Theory*, ch. 17 and 19 (explicit formulae).

## Open
* A lower bound for $\lambda_{\min}(G_N)$ under RH, even $\exp(-N^A)$.
* A version of the conjecture that survives §4, §5 and §7. For ζ itself both forms are now proved under RH, so each is equivalent to RH (`PivotSharp.rh_iff_orbitLattice`, `PivotSharp.rh_iff_shortest`; [ball-rate.md](../formalisations/ball-rate.md)).
* Whether the shortest-vector form holds for the Frobenius orbit of every curve. It does when the minimal polynomial of Frobenius is irreducible (§7).
* The limiting Euclidean eigenvector, and the effective functional that selects it.
* Whether a bounded number of pivots decides $d_k\ge d_1$ for every Dirichlet $L$-function (§5.1). For real characters, whether $d_2$ alone decides it beyond $q\le10^4$; if so, [d2-density.md](d2-density.md) gives the density of failures of the whole conjecture.

*Prepared with AI assistance (Grok Bot). Certified numbers rest on python-flint/arb ball arithmetic; everything marked Numerical is floating point.*
