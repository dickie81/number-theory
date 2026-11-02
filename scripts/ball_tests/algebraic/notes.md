# The orbit Gram matrix near its "horizon": exact structure

Notation. $G_N(m,n)=\sqrt{mn}\,K_H(m/n)$, $K_H(r)=\sum_\rho r^{\rho-1/2}/(\rho(1-\rho))$ (zeros with multiplicity, symmetric summation),
$d_1=K_H(1)=\sum_\rho 1/(\rho(1-\rho))=2+\gamma-\log 4\pi$. For $v\in\mathbb R^N$ put $V(s)=\sum_{n\le N}v_n n^{s}$.
Checks: `checks.py` (numbers below), data from `../spread`, `../horizon`.

## 1. Exact forms (proved)

**Prop 1 (zero-sum form).** $\sqrt{mn}(m/n)^{\rho-1/2}=m^{\rho}n^{1-\rho}$, so unconditionally
$$v^{T}G_Nv=\sum_\rho \frac{V(\rho)\,V(1-\rho)}{\rho(1-\rho)} .$$
Under RH, $1-\rho=\bar\rho$, $\rho(1-\rho)=|\rho|^2$ and $V(\bar\rho)=\overline{V(\rho)}$ ($v$ real):
$$v^{T}G_Nv=\sum_\rho \frac{|V(\rho)|^2}{|\rho|^2}\ \ (\ge 0).$$
So $G_N$ is the Gram matrix of $w_n=(n^{\rho})_\rho$ in $\ell^2(\text{zeros},|\rho|^{-2})$: a Weil-type form, the zero side of the explicit formula.
(Absolute convergence: $|V(\rho)|\le\sum|v_n|n^{1/2}$ and $\sum|\rho|^{-2}<\infty$.)

**Prop 2 (closed form).** For $x\ge1$, $K_H(x)=\sqrt x\,(\sum_{n\le x}\Lambda(n)(1/n-1/x)-\log x+1+\gamma-\log(2\pi)/x+t(1/x))$, $t(y)=y+\tfrac12(1-y)\log(1-y)-\tfrac12(1+y)\log(1+y)$.
Proof: $f(x)=\sum_\rho x^\rho/(\rho(1-\rho))$; integrate the explicit formula $\psi_0(t)=t-\sum_\rho t^\rho/\rho-\log2\pi-\tfrac12\log(1-t^{-2})$ against $t^{-2}dt$ on $[1,x]$; termwise integration is legitimate by bounded convergence of symmetric partial sums on compacts (Davenport ch. 17); $\int_1^x t^{\rho-2}dt/\rho=(1-x^{\rho-1})/(\rho(1-\rho))$, giving $f(x)/x=d_1+\int_1^x(\psi_0(t)-t+\log2\pi+\tfrac12\log(1-t^{-2}))t^{-2}dt$; the last integral is elementary. (Same for Dirichlet $L$, see ../dirichlet/dcore.py.)

**Prop 3 (monotone limit).** $\lambda_N:=\lambda_{\min}(G_N)$ is non-increasing in $N$ (Cauchy interlacing), so $\lambda_\infty=\lim\lambda_N\ge0$ exists (under RH).

**Prop 4 (difference variables; flat-model pencil).** $M=(\min(m,n))=BB^{T}$, $B$ lower-triangular ones. With $u=B^{T}v$, i.e. $u_k=\sum_{n\ge k}v_n$, $v_n=u_n-u_{n+1}$ ($u_{N+1}=0$):
$v^TMv=\|u\|^2$ and $v^TGv=u^THu$, $H(j,k)=G(j,k)-G(j-1,k)-G(j,k-1)+G(j-1,k-1)$ ($G(0,\cdot)=0$). In zeros (RH):
$$u^THu=\sum_\rho\frac{|\sum_j u_j\,(j^{\rho}-(j-1)^{\rho})|^2}{|\rho|^2},\qquad j^\rho-(j-1)^\rho=\rho j^{\rho-1}(1+O(|\rho|/j)).$$
So for $|\gamma|\ll j$ the weight $|\rho|^{-2}$ is cancelled: $H$ is (to leading order) the *unweighted* Gram of $j^{\rho-1}$ over zeros up to height $\asymp j$. $\lambda_{\min}(G,d_1M)=\lambda_{\min}(H)/d_1$.

## 2. Test vectors (proved asymptotics, RH)

**Prop 5 (harmonic vector is not near-null).** $v_n=1/n$: by Euler–Maclaurin with $w=1-\rho$ and $\zeta(1-\rho)=0$,
$V(\rho)=\sum_{n\le N}n^{\rho-1}=\zeta(1-\rho)+\frac{N^\rho}{\rho}+\tfrac12N^{\rho-1}+O(|\rho|N^{-3/2})=\frac{N^\rho}{\rho}+O(N^{-1/2}+|\rho|N^{-3/2})$.
Hence $v^TGv=N\,S_4+O(\log^2N)$, $S_4=\sum_\rho|\rho|^{-4}=7.41981\times10^{-5}$, and Rayleigh $=N S_4/\zeta(2)(1+o(1))$.
Check: Rayleigh$/N$ = 4.5533e-5 (N=1000), 4.5130e-5 (6000); $S_4/\zeta(2)$ = 4.5107e-5. ✓
Meaning: the only obstruction for $1/n$ is the *boundary term* $N^\rho/\rho$ from the cut at $n=N$ ("the horizon is at $n\approx N$").

**Theorem 6 ($\lambda_\infty=0$, with rate; RH).** $v_n=(-1)^{n-1}/n$ gives $V(\rho)=\eta(1-\rho)-\sum_{n>N}(-1)^{n-1}n^{\rho-1}$ and $\eta(1-\rho)=(1-2^{\rho})\zeta(1-\rho)=0$. The tail is $\pm\tfrac12N^{\rho-1}+O(|\rho|N^{-3/2})$. For $|\gamma|\le N$ this gives $|V(\rho)|^2\ll 1/N+\gamma^2/N^3$; for $|\gamma|>N$ use the discrete mean value over zeros (Gallagher/Montgomery large-sieve type: $\sum_{T<\gamma\le2T}|\sum_{n\le N}a_nn^{i\gamma}|^2\ll(T+N)\log T\sum|a_n|^2$, $a_n=\pm n^{-1/2}$). Summing dyadically,
$$\lambda_{\min}(G_N)\le\frac{v^TGv}{\|v\|^2}\ll\frac{\log^2N}{N}\to0 .$$
Check: Rayleigh(alt) = 1.052e-3 (N=1000), 2.207e-4 (6000); $\lambda_{\min}$/Rayleigh(alt) = 0.333, 0.321, 0.315, 0.311, 0.309 (N=100…6000) — same order as $\lambda_{\min}$, numerically Rayleigh(alt) $\approx 0.15\,\log N/N$. (Proof sketch: the zero mean-value input is standard but I have not written the constants.)

**Prop 7 (formal kernel vectors).** Let $A(z)=\sum a_n n^{-z}=\zeta(1+z)H(z)$ with $H$ a Dirichlet series, i.e. $v=(1/n)*h$, $n v_n=\sum_{d\mid n}d\,h(d)$. Then formally $V(\rho)=A(-\rho)=\zeta(1-\rho)H(-\rho)=0$ at every zero. Truncation at $N$ leaves the boundary term $H(0)N^{\rho}/\rho+\dots$; so the series *converges* to 0 at the zeros iff (essentially) $H(0)=0$ (example: $H=1-2^{-z}$, $v=(-1)^{n-1}/n$). These $v\in\ell^2$ are "kernel vectors" not in the form domain of finite truncations: every finite truncation has $v^TGv>0$ (PD), and the value tends to 0 only through the boundary layer. **No finitely supported kernel vector exists** whenever $G_N$ is PD, i.e. whenever $\{n^\rho\}_{n\le N}$ is linearly independent as functions on the zeros (true if e.g. the zeros are not all in a finite union of arithmetic progressions; numerically certified PD for $N\le500$).

## 3. The two numerical eigenvectors, explained

**(a) Euclidean bottom eigenvector** (frozen, 97.5% on $n<16$, overlap 0.998 across N=100…6000). It is a Prop-7-type object: $f(n)=n v_n$ is very nearly multiplicative (mean error 0.005 on coprime $ab\le200$ at N=6000), with $f(p^k)$ almost constant in $k$ ($f(2,4,8,16)=0.670,0.622,0.609,0.607$; $f(3,9,27)=0.749,0.726,0.722$; $p(1-f(p))\to\approx1$). That is the shape $v=(1/n)*h$ with $h$ supported on squarefree $d$ and $h(p)\approx -p^{-2}\cdot c_p$, $c_p\to1$ — close to (but measurably not equal to) $\varphi(n)/n^2$ ($A=\zeta(1+z)/\zeta(2+z)$, $f(p)=1-1/p$). Since $H(0)\neq0$ the boundary term is cancelled by an edge layer at $n\sim N$ (sign changes in the tail: 20 at N=1000, 72 at N=3000) of $\ell^2$-cost $O(1/N)$. **Conjecture A:** $v^{(N)}\to v^\infty$ in $\ell^2$, $v^\infty_n=f(n)/n$ with $f$ multiplicative, and $v^\infty$ is a formal kernel vector ($A^\infty(-\rho)=0$ in the Abel sense) not attained at finite N. I could not identify $f$ in closed form; $f(2)$ extrapolates to ≈0.65–0.66, not 1/2.

**(b) Flat-pencil eigenvector = harmonic vector + edge layer.** $n v_n=1.00\text{–}1.08$. The "travelling wave" at $j\approx\log_2N-3$ is exactly the cumulative-sum image of $1/n$: $u_k=\sum_{k\le n\le N}1/n\approx\log(N/k)$, so the M-weight of block $j$ is $\approx\int_{2^j}^{2^{j+1}}\log^2(N/k)dk\propto 2^j(J-j)^2$ ($J=\log_2N$), maximal at $J-j=2/\ln2\approx2.89$. Predicted vs measured blocks, N=6000: pred [.007 .011 .017 .027 .042 .063 .093 .129 .165 .186 .167 .088 .007], meas [.006 .009 .015 .024 .038 .058 .086 .123 .162 .191 .182 .100 .005]. ✓ So "smearing to the horizon" in (b) is not dynamics: it is $\log(N/k)$, the potential of the harmonic vector in difference variables; the weight on any fixed block decays like $\log^2N/N$ (k<16: pred 0.047 vs meas 0.055 at N=6000).
The pencil is so small ($\sim N^{-2}$) because the M-norm of $1/n$ is $\asymp N$ while the edge layer removes $N^\rho/\rho$; an analytic derivation of the exponent ($N^{-1.97}\log^{0.75}N$ fit) is **not** done.

## 4. Burnol / Báez-Duarte

* $d_1=\sum_\rho 1/|\rho|^2=2+\gamma-\log4\pi$ is exactly Burnol's constant (for simple zeros; in general Burnol has $\sum m_\rho^2/|\rho|^2$, $d_1=\sum m_\rho/|\rho|^2$). Báez-Duarte: $d_N^2=\inf_A\frac1{2\pi}\int_{\Re s=1/2}|1-\zeta(s)A(s)|^2\frac{|ds|}{|s|^2}$, $A$ Dirichlet polynomial of length $N$; RH $\iff d_N\to0$. Burnol (2002): $\liminf d_N^2\log N\ge\sum_\rho m_\rho^2/|\rho|^2$. Mechanism: $1-\zeta A=1$ at each zero, so the zero part of that norm is $\|w_1\|^2=d_1$ in our language; Burnol's bound says Dirichlet polynomials of length $N$ (of the form $\zeta A$) cannot cancel the $w_1$-component faster than $1/\log N$.
* Our orbit is the *unrestricted* version: $\mathrm{dist}^2(w_1,\mathrm{span}(w_2..w_N))=1/(G_N^{-1})_{11}$ = 2.98e-3, 4.17e-4, 8.55e-5 (N=100,1000,6000), i.e. $\approx N^{-0.87}$, much faster than Burnol's $1/\log N$ (times $\log N/d_1$: 0.30, 0.062, 0.016 → 0). So the orbit does not inherit Burnol's lower bound; the distinction is that B–D approximants must have the form $\zeta(s)A(s)$ on the whole line, while ours only see the zeros.
* The analogue of Burnol's question for us is the rate of $\lambda_N$: Theorem 6 gives $\lambda_N\ll\log^2N/N$; numerics (certified at N=100,300,1000) give $\lambda_N\approx c\log^{0.89}N/N$. A matching lower bound $\lambda_N\gg 1/N$ is **open** (Conjecture B).

## 5. "Horizon" statements

**Theorem H (RH).** (i) $G_N\succ0$ for each $N$ for which $\{n^\rho\}_{n\le N}$ is independent on the zeros (certified numerically to N=500); (ii) $\inf_N\lambda_{\min}(G_N)=0$, with $\lambda_{\min}(G_N)\ll\log^2N/N$; (iii) the infimum is not attained by any finitely supported vector; the minimising sequences converge (e.g. $(-1)^{n-1}/n$ truncations) to $\ell^2$ vectors whose Dirichlet series vanish at every zero but which are outside the domain of finite truncations; the cost of truncation is a boundary term $\propto N^{\rho}$ at $n\approx N$.
In the BH language: the "horizon" is the boundary layer at $n\approx N$; a zero-norm (null) vector exists only "at $N=\infty$", never at finite $N$ — the defect $\lambda_N\to0$ but is positive for every $N$.
**Contrast (proved, ../ff_pivots):** for a curve over $\mathbb F_q$ there *are* finitely supported null vectors (on $\{n,nq,\dots,nq^{2g}\}$), because $q^{i\gamma}$ takes finitely many values; the horizon is crossed at $N=q^{2g}$.
**Conjecture B:** $\lambda_{\min}(G_N)\asymp\log N/N$. **Conjecture A:** as in §3(a). **Pivot conjecture** $d_k\ge d_1$: unaffected by any of this (pivots are distances, not eigenvalues); known false for many Dirichlet $L$ (../hunt), certified true for zeta $k\le500$.

## Caveats
Theorem 6's large-$\gamma$ step uses a standard discrete mean-value theorem over zeros that I cite rather than reprove; constants not computed. Props 5–7 and §3 explanations are checked numerically in double precision. Conjecture A's $f$ is not identified. The $N^{-2}$ law of the pencil is only fitted.
