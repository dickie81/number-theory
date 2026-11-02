# Density of real characters with d2 < d1

Real primitive chi mod q, parity a, l = L'/L(1,chi). This uses Theorem B (docs/ball-conjecture-tests.md, branch ball-conjecture-tests).
1. K1 > 0 unconditionally: Re 1/(rho(1-rho)) = (b(1-b)+g^2)/|rho(1-rho)|^2 > 0.
2. d2 >= d1 iff -2K1-2c_a <= l <= -2c_a, where c0 = -(1/4)log(27/4) and c1 = (3/4)log(3/4). Lean: lean/D2Criterion.lean (no sorry).
3. Thresholds: even l > (1/2)log(27/4) = 0.95477, odd l > (3/2)log(4/3) = 0.43152. In terms of the Euler-Kronecker constant gamma_K = gamma + l, these are gamma_K > 1.5320 and gamma_K > 1.0087.
   Both have tau >= 1, which is inside the unconditional range of Lamzouri, JMAA 2015 (arXiv:1410.1603), Thm 1.1.
4. Predicted density: (1/2)(P(X > t0) + P(X > t1)) = (1/2)(0.051123 + 0.160911) = 0.10602.
   Lamzouri's theorem is stated for all fundamental discriminants D. The split by sign of D is needed here and is NOT stated in that paper (assumed routine).
   The lower-threshold failures have density 0 (the threshold is about -0.4 log q).
Data (ratio fail/n, z vs limit):
 q<=1e4: even 0.0503 (z=-0.2), odd 0.1591 (z=-0.3)
 20k-25k: even 0.0587 (z=1.35), odd 0.1764 (z=1.65)
 60k-64k: even 0.0699 (z=2.97), odd 0.1744 (z=1.29)
 Empirical sd of l rises toward the model sd 0.8635 (even: 0.65, 0.755, 0.796). So convergence is slow and the
 q<=1e4 agreement was a coincidence of shape. Data in this range do not confirm the constant.

## Extension to complex characters (heuristic, not proved)
Exact: with l=u+iv and L0=log(q/pi)+psi_a, d2<d1 iff (L0+2c_a+3u)^2+v^2 > (L0+2u)^2.
As q -> infinity this tends to: u > -2c_a (the same thresholds).
Model with chi(p) uniform on the circle (cplx.py, Monte Carlo, 4e5 samples, p<2e4): P(u>0.9548)=0.0599, P(u>0.4315)=0.2579, density about 0.159.
Observed for all primitive characters with q<=400 (PR #75): 0.203. The finite-q correction is large here, so this is not a check.
Rigour would need a limiting distribution for L'/L(1,chi) over all characters (Ihara-Matsumoto type, GRH), with the parity split.

## Large-q test (PARI lfun via cypari2; agrees with flint to all printed digits at q~6e4)
Random samples of fundamental D in each window, by sign. Rate = #(l > t_a)/n. No lower failures are possible: min l is far above the lower threshold.
 [1e5,1.2e5]    +: 0.0653 (n=3000, z=+3.5)  -: 0.1847 (z=+3.5)
 [1e6,1.05e6]   +: 0.0514 (n=5000, z=+0.1)  -: 0.1670 (z=+1.2)   combined 0.1092±0.0031
 [1e7,1.01e7]   +: 0.0490 (n=5000, z=-0.7)  -: 0.1646 (z=+0.7)   combined 0.1068±0.0031
 [1e8,1.001e8]  +: 0.0552 (n=2500, z=+0.9)  -: 0.1668 (z=+0.8)   combined 0.1110±0.0044
Prediction 0.0511 / 0.1609 / 0.1060. sd(l) reaches the model's 0.8635 by 1e7.
Truncating the random model at p<=y gives LOWER tail probabilities (y=100: 0.045/0.155), so prime truncation
does not explain the 1e4–1e5 excess. Its cause is unexplained (a moderate-range effect, gone by 1e6).
