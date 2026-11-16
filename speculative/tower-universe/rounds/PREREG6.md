# Pre-registration, round 6: are the prime packets identical quanta?

Written 2026-11-06, before computing.

A packet is a prime p and the integers after it, up to the next prime q. Its effect on the thinnest axis is

  Δ_packet = 1/λ_{q−1} − 1/λ_{p−1}.

Of that, the prime's own share is Δ_prime = 1/λ_p − 1/λ_{p−1}. Here p ≤ 2048, and λ_N is computed exactly at
N = p − 1 and N = p.

**Units.** Express both in units of the mean increment per integer over the same dyadic window ("integers' worth").

**Report:**
- the prime's median share of its packet;
- a fit of Δ_packet against the gap g = q − p;
- Spearman's ρ between Δ_packet and g.

**Decision.**
- **Identical quanta**: the share is ≥ 80% and Δ_packet does not grow with g (|ρ| < 0.2).
- **Otherwise**: the packet's size is set by its gap.
