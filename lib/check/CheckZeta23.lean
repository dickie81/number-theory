/- This file prints the axioms of the final theorems of the `lib/zeta23` layer, the modules that also use the vendored
`zeta23`. `CheckAll.lean` cannot print them: zeta23's files under `Zeta23/FromPNTPlus/` repeat top-level names of
`lib/vendor/pnt-plus` (`div_cpow_eq_cpow_neg` and `ResidueOfTendsTo` in `ZetaBounds`, for example), and `CheckAll`
imports PrimeNumberTheoremAnd. It is not built by default (`scripts/check_axioms.py --zeta23`). Every line it prints
must be `[propext, Classical.choice, Quot.sound]`, a subset of them, or none. -/
import BohrLandau
import ShellSixth
import ZeroWindow
import HybridCertificate
import CriticalLine

/- The zeros on the critical line: Hardy's theorem, Selberg's positive proportion, the same for the simple zeros, and
Alpöge and Furman's Theorems A, B and C as zeta23 proves them, with no hypothesis. -/
#print axioms CriticalLine.exists_zero_im_gt
#print axioms CriticalLine.infinite_zeros
#print axioms CriticalLine.ncard_zeros_ge
#print axioms CriticalLine.ncard_simple_zeros_ge
#print axioms CriticalLine.infinite_simple_zeros
#print axioms CriticalLine.two_thirds
#print axioms CriticalLine.two_thirds_cumulative
#print axioms CriticalLine.half_simple
#print axioms CriticalLine.three_quarters_distinct

/- `S(T) = O(log T)` for the library's zeros of `riemannZeta`, from zeta23's Riemann–von Mangoldt formula, and the
bounded gaps between their ordinates that it gives. -/
#print axioms SlogZeta.Slog_eventually
#print axioms SlogZeta.Slog_zeta
#print axioms SlogZeta.wall_law_zeta_S
#print axioms ZeroWindow.zero_in_window

/- Almost every zero is within `w` of the critical line: for `w > ¼` by the density estimate `DensityXi (4(1+δ)) 11`,
for `w > 1/6` by the Euler–Maclaurin approximation, and for every `w > 0` (Bohr and Landau); each with the lower
bound of `ShellDensity.NX_zero_ge`, at least `T log T / 8π` zero pairs up to height `T`. -/
#print axioms CountCompare.local_count_le
#print axioms ShellDensity.emBound_zeta23
#print axioms ShellDensity.density_zeta23
#print axioms ShellDensity.Ncount_le_NX
#print axioms ShellDensity.NX_zero_ge
#print axioms ShellDensity.tendsto_NX_div_quarter
#print axioms ShellDensity.tendsto_outside_div_quarter
#print axioms ShellDensity.ncard_outside_le_unconditional
#print axioms ShellSixth.emApprox_zeta23
#print axioms ShellSixth.tendsto_NX_div_sixth
#print axioms ShellSixth.tendsto_outside_div_sixth
#print axioms BohrLandau.tendsto_NX_div_pos
#print axioms BohrLandau.tendsto_outside_div_pos

/- The same-space hybrid certificate on zeta23's zero side, for any zero-block data. -/
#print axioms HybridCert.cert_general
#print axioms HybridCert.cert_offline
#print axioms HybridCert.hybrid_cert
#print axioms HybridCert.hybrid_cert_pairs
#print axioms HybridCert.hybrid_cert_of_offline
#print axioms HybridCert.hybrid_cert_of_moments
#print axioms HybridCert.hybrid_cert_of_no_offline
#print axioms HybridCert.hybrid_cert_eta_zero
