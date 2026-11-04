# The limiting Euclidean bottom eigenvector of the zeta orbit Gram matrix

Data: `eig_big.py` (double precision, N = 300…8000), `extrap.py`, `eig_big.json`, `f_extrap.json`. $f(n)=n v_n/v_1$.

## Accuracy
Residual-based Davis–Kahan bound on the eigenvector angle: $\le r/(\lambda_2-\lambda_1)$ = 1.8e-11 (N=300), 3.5e-10 (1000), 2.6e-7 (8000).
Gap $\lambda_2-\lambda_1\approx 2.9\lambda_1$ throughout. So double precision is ample; the uncertainty is the N→∞ drift, not arithmetic. (No mpmath rerun was needed for that reason.)

## Finite-N data (N = 8000)
f(2..5) = 0.6690, 0.7473, 0.6205, 0.8290; f(7)=0.8704, f(8)=0.6097, f(9)=0.7278, f(16)=0.6045, f(27)=0.7265.
Multiplicativity on coprime $ab\le100$: max error 0.011, mean 0.0033.
Primes: $(p+1)(1-f(p))$ = 0.993, 1.011, 1.026, 1.037, 1.053 for p = 2, 3, 5, 7, 11, rising slowly with p (edge-layer contamination grows with n).
So **empirically $f(p)\approx p/(p+1)$** (to 1–5% for p ≤ 11). Prime powers do not follow $n/\psi(n)$ ($\psi$ = Dedekind psi, which would give $f(p^k)=p/(p+1)$): $f(2^k)$ = 0.669, 0.621, 0.610, 0.605, 0.604; $f(3^k)$ = 0.747, 0.728, 0.727.
Möbius differences $g=\mu*f$: $g(2,4,8,16)$ = −0.331, −0.049, −0.011, −0.005; $g(3,9,27)$ = −0.253, −0.020, −0.001; $g(5,25)$ = −0.171, −0.004.
Candidates rejected: $\varphi(n)/n$ (f(2)=1/2), complete multiplicativity (f(4)≠f(2)²), $h(p)=-1/p^2$ (gives f(p)=1−1/p).

## N-dependence
f(2) for N = 300…8000: 0.6819, 0.6802, 0.6790, 0.6773, 0.6772, 0.6737, 0.6737, 0.6714, 0.6700, 0.6690. That is a drift of about −0.004 per doubling of N, superposed on oscillations (from $N^{i\gamma}$). Fitting $a+b/\log N$ gives $f_\infty(2)\approx0.647$, $f_\infty(3)\approx0.740$, $f_\infty(4)\approx0.579$. A quadratic in $1/\log N$ gives wildly different values (0.608, 0.654, 0.696). The extrapolated vectors are *less* multiplicative (mean error 0.04 and 0.22) than the raw ones. **Conclusion: the N→∞ limit cannot be pinned down from N ≤ 8000.** It is not even clear that the limit exists: a drift ∝ 1/log N is consistent with the data, and so is a slow logarithmic divergence.

## Theory: why the formal variational problem does not determine the limit
Formal kernel vectors are $v=(1/n)*h$, i.e. $\sum v_nn^{-z}=\zeta(1+z)H(z)$, with $f=1*(\mathrm{Id}\cdot h)$ and $f(1)=h(1)=1$.
**Prop.** $\inf\{\|v\|^2: v \text{ formal kernel},\ v_1=1\}=1$, and it is not attained.
Proof: take $H_y(z)=\prod_{p\le y}(1-p^{-1-z})$. Then $v_n=1/n$ for $y$-rough $n$ (no prime factor ≤ y), else 0, and $\|v\|^2=1+\sum_{n>1,\ y\text{-rough}}n^{-2}\to1$ as $y\to\infty$. The limit $e_1$ is not a kernel vector, because $V(\rho)=1$.
So "minimise the norm subject to formal vanishing" is degenerate. The true limit is selected at the next order, by the boundary cost of truncating at N.
For $v=(1/n)*h$ (with h finitely supported) truncated at N, $V_N(\rho)=-H(0)N^{\rho}/\rho+\dots$. Removing that boundary term needs an edge layer at $n\asymp N$ costing $\asymp H(0)^2/N$ in $\ell^2$. When $H(0)=0$ (e.g. $(-1)^{n-1}/n$) the next terms dominate. All competitors (the alternating vector: 0.15 log N/N; the true minimum: about 0.047 log N/N) come in at order $\log N/N$. So the limit eigenvector is the minimiser of an effective $\log N/N$-coefficient functional. That functional involves the zero sums $\sum_\rho|\rho|^{-2}N^{i\gamma}\cdots$, whose oscillation explains the non-monotone drift. I have not derived the functional in closed form.

## Status
* No closed form found. Best description: $f$ is approximately multiplicative (to 1%), with $f(p)\approx p/(p+1)$ for small p at finite N, prime-power factors decreasing to about 0.60 (p=2) and 0.73 (p=3), and $g=\mu*f$ concentrated on primes ($g(p)\approx-1/(p+1)$, $|g(p^2)|\lesssim0.05$).
* Proved: the formal constrained problem is degenerate (Prop. above), so no "Lagrange-multiplier $H$" exists for it.
* Open: whether $v^{(N)}$ converges at all; the effective functional; the Rayleigh constant $c$ in $\lambda_N\sim c\log N/N$ (fit: $\lambda_N N/\log N$ = 0.051, 0.048, 0.047 at N = 100, 1000, 3000).
