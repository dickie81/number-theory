# Signed estimate (`weighted_chi_a`)

Scripts for the Batch-7 deep dive and follow-up: can `χ̄(a)`-weighted cancellation
replace (part of) zero-density in the Linnik deduction at `σ = 5/7`, for prime `q`?

| script | role |
|---|---|
| `bookkeeping.py` | Exact `Z(a)` target; savings for `L < 11/5`, `2.198`, `2.167`; random-phase heuristic `L` |
| `heuristic_random_phases.py` | Monte Carlo random-phase `Z(a)`; empirical `α` |
| `synthetic_Z.py` | **SYNTHETIC** off-line zeros at `σ=5/7` + GRH-on-the-line model |
| `real_zeros_Z.py` | Low-lying zeros via truncated Dirichlet series for `q ∈ {5,7,11,13}` only |
| `tao_uncertainty.py` | Tao on additive `F_q`; spike construction; amplifier windows |
| `second_moment_positivity.py` | Plancherel / moments / one-sided Fejér proxy |
| `barrier_linear_zeros.py` | **Barrier:** linear-in-`k` zeros achieving `Z(a0)/△ = 1` |
| `large_sieve_k.py` | Large-sieve / Tao on `(Z/q)* ≅ Z/(q-1)` — no every-`a` obstruction |
| `function_field_model.py` | FF proxy: RH-random, adversarial off-line, exact tiny prime counts |
| `circularity_check.py` | Every-`a` saving ≡ PNT-in-AP at same scale (circularity) |
