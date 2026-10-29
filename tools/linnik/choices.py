"""The certificate's choices at depths two and four, from mirror2.py's definitions: the paper's Section 5.5 figures.

    python3 tools/linnik/choices.py [U1 U2 N]      # default: the library's window 41556 47531 and N = 340

It prints:
- the candidate cells of depth two, how many the sharp rule allows, and how many candidate cells have
  Delta^dec_2 > (Delta_2 - kappa)_+ (none on the library's grid, so that a candidate cell is decomposed exactly when
  the sharp rule allows it);
- the counted cells of depth four below the decomposed candidate cells, how many the sharp rule allows, how many of
  those are decomposed, how many counted cells have Delta^dec_4 > Delta_4, and what the counted cells that the sharp
  rule forbids would save decomposed;
- the dropped candidate cells that reach the line alpha_1 + alpha_2 = 1 - U_1/D, and their cost.
Delta^dec is computed as the Lean's refcost: at depth four with the sharp rule, as in the certificate. About a minute
on four cores. These are computations, not theorems of the library.
"""
import os
import sys
from multiprocessing import Pool

args = sys.argv[1:] or ['41556', '47531', '340']
sys.argv = [sys.argv[0]] + args
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mirror2 as m  # noqa: E402  (mirror2 reads the window and N from sys.argv)

DEN, H, HC, E, EC, n, nC, lim = m.DEN, m.H, m.HC, m.E, m.EC, m.n, m.nC, m.lim
sums, inside, extend = m.sums, m.inside, m.extend


def row(i):
    """The candidate cells (i, j) of depth two, each with its sharp-rule test, its costs and its depth-four cells."""
    ei = E[i]
    out = []
    for j in range(n):
        ej = E[j]
        if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (m.U1 < ei and ei + H < m.U2)):
            continue
        if any(inside(a, b) for a, b in sums([(ei, H), (ej, H)])):
            continue
        allowed = ei + H + (ej + H) < lim
        ks = []
        for k in range(n):
            ek = E[k]
            if ek < ej + H and ei + ej + 2 * ek <= DEN:
                S3 = sums([(ei, H), (ej, H), (ek, H)])
                if not any(inside(a, b) for a, b in S3):
                    ks.append((k, S3))
                    if not (ei + H + (ej + H) + (ek + H) < lim):
                        allowed = False
        ref = 0                       # Delta^dec_2, the cost if decomposed
        c4 = a4 = d4 = over4 = 0      # counted, allowed, decomposed, with Delta^dec_4 > Delta_4
        forbidden_saving = 0          # what the forbidden counted cells would save decomposed
        for k, S3 in ks:
            ek = E[k]
            for l in range(k + 1):
                el = E[l]
                if not (ei + ej + ek + 2 * el <= DEN) or extend(S3, el, H):
                    continue
                c4 += 1
                S4 = ei + ej + ek + el
                T4 = S4 + 4 * H
                allowed4 = T4 < lim
                b4 = m.bound4(ei, ej, ek, el)
                S4s = sums([(ei, H), (ej, H), (ek, H), (el, H)])
                ne5 = []
                for b in range(nC):
                    eb = EC[b]
                    if eb < el + H and S4 + 2 * eb <= DEN and not extend(S4s, eb, HC):
                        ne5.append(b)
                        if not (T4 + eb + HC < lim):
                            allowed4 = False
                r5 = 0                # Delta^dec_4
                for b in ne5:
                    eb = EC[b]
                    S5s = S4s + [(a + eb, c + eb + HC) for a, c in S4s]
                    for c in range(b + 1):
                        ec = EC[c]
                        if S4 + eb + 2 * ec <= DEN and not extend(S5s, ec, HC):
                            r5 += m.bound6(ei, ej, ek, el, eb, ec)
                if r5 > b4:
                    over4 += 1
                if allowed4:
                    a4 += 1
                    if r5 <= b4:
                        d4 += 1
                        ref += r5
                    else:
                        ref += b4
                else:
                    ref += b4
                    forbidden_saving += max(b4 - r5, 0)
        b2 = m.bound2(ei, ej)
        s2, _ = m.sub2(i, j)
        out.append((allowed, ref, b2, s2, c4, a4, d4, over4, forbidden_saving, ei + ej + 2 * H >= lim))
    return out


def main():
    with Pool(4) as p:
        cells = [c for r in p.imap_unordered(row, range(n), chunksize=1) for c in r]
    K = m.K
    total2 = 0
    n_allowed = over2 = 0
    c4 = a4 = d4 = over4 = 0
    saving = 0
    reach_n = reach_cost = 0
    for allowed, ref, b2, s2, cc4, ca4, cd4, cover4, csave, reach in cells:
        kept = max(b2 - s2, 0)
        if ref > kept:
            over2 += 1
        if allowed:
            n_allowed += 1
            cost = ref if ref <= b2 else kept
            c4 += cc4
            a4 += ca4
            d4 += cd4
            over4 += cover4
            saving += csave
        else:
            cost = kept
            if reach:
                reach_n += 1
                reach_cost += cost
        total2 += cost
    print(f'total2 = {total2} = {total2 / K:.7f} K')
    print(f'candidate cells {len(cells)}, allowed by the sharp rule {n_allowed}; '
          f'with Delta^dec_2 > (Delta_2 - kappa)_+: {over2}')
    print(f'counted cells of depth four below the decomposed ones {c4}, allowed {a4}, decomposed {d4}; '
          f'with Delta^dec_4 > Delta_4: {over4}; the forbidden ones would save {saving / K:.4f} K decomposed')
    print(f'dropped candidate cells reaching alpha_1 + alpha_2 = 1 - U_1/D: {reach_n}, cost {reach_cost / K:.4f} K')


if __name__ == '__main__':
    main()
