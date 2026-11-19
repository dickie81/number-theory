#!/usr/bin/env python3
"""The Linnik paper's figure of where the two certificates' cost lies (`papers/linnik-exponent/fig-cost.tex`).

    python3 tools/linnik/fig_cost.py            write the figure's file
    python3 tools/linnik/fig_cost.py --check    fail if the file on disk differs from what would be written
    python3 tools/linnik/fig_cost.py --table    the pieces, and the share of each cost in some ranges

The bound of the first term is a chain of pieces over the first prime's range: `tree21500` in `Linnik21500.lean`
(Theorem 1.2, at `43/20`) and `tree21000` in `Linnik21000.lean` (Theorem 1.1, at `21/10`), each `pr_mono` of a chain
of `pr_split`. A piece is one of two kinds:

* a cell `node<tag>_i : PR [(a, b)] false c`, in `Linnik21500.lean` or in `SieveHint21000N<j>.lean`;
* a part `tree<tag>_k : (partD solve<tag> TOP [] false [cuts] A K HINT).1 ≤ c`, in a part file that the root's file
  imports: the range `[A, TOP)`.

The range is in units of `1/DEN` of the exponent of `x` (`DEN = 2^40`), and the cost `c` in units of `1/K`
(`K = 2^60`); the script reads `DEN` and `K` from `SieveCertDefs.lean`, `L` from `route<tag>`, and everything else
from the theorems' statements. Only the pieces at the top level of the root's chain count; the files also hold the
cells of later primes. A hint is never read whole: of a long line the script keeps its two ends. The script stops if
the pieces do not tile `[f_*, DEN/2 + 1)` in order, if a cost is not below `K`, or if the costs do not add up to the
root's total exactly. (`pr_mono` would allow a sum below the total, but then the area under a curve would not be the
certificate's cost, as the caption says.)

The figure plots, for each certificate, the step function that is `(c/K)/((b − a)/DEN)` on each piece: the cost per
unit of the first prime's exponent, `log p₁/log x`. The area under it is the certificate's cost `c/K`, so the axis is
linear and starts at `0`. A part covers several cells; it is drawn as one step, at its average. The last piece of
each, `[0.4995, 0.5]`, is far higher than the rest (above 9, against at most 5.7): the axis stops at `6`, the two
steps are cut there with a break mark, and a label gives their heights. Thin gray lines mark the two floors `f_*/D`,
where the steps start. `--table` prints each
piece and, for each certificate, the area on `[f_*, 0.2]`, `[0.2, 0.3]`, `[0.3, 0.4]` and `[0.4, 0.5]` (a piece cut
by an end in proportion to its length), and the exponent above which half the cost lies.

Needs Python 3 only. It reads the 58 files of the cells at `21/10` (24 MB) in under a second.
"""
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PNT = os.path.join(ROOT, 'lib', 'pnt')
OUT = os.path.join(ROOT, 'papers', 'linnik-exponent', 'fig-cost.tex')
TAGS = ['21500', '21000']        # Theorem 1.2 (43/20), then Theorem 1.1 (21/10)
HEAD = 4096                      # the bytes kept from each end of a long line (a hint)


def lines(path):
    """The lines of a file, each without its end; of a line longer than `2·HEAD` bytes (a hint) only its first and
    last `HEAD` bytes, joined by ` … `, so that a hint is never held whole."""
    with open(path, 'rb') as f:
        while True:
            line = f.readline(2 * HEAD)
            if not line:
                return
            if line.endswith(b'\n') or len(line) < 2 * HEAD:
                yield line.decode().rstrip('\n')
                continue
            head, tail = line[:HEAD], line[HEAD:]
            while not tail.endswith(b'\n'):
                chunk = f.readline(1 << 20)
                if not chunk:
                    break
                tail = (tail + chunk)[-HEAD - 1:]
            yield head.decode('ascii', 'replace') + ' … ' + tail[-HEAD - 1:].decode('ascii', 'replace').rstrip('\n')


def power(s):
    """`2 ^ 40` or a numeral, as an integer."""
    m = re.fullmatch(r'\s*(\d+)\s*\^\s*(\d+)\s*', s)
    return int(m.group(1)) ** int(m.group(2)) if m else int(s)


def constants():
    """`DEN` and `K` of `SieveCert` (`SieveCertDefs.lean`)."""
    got = {}
    for line in lines(os.path.join(PNT, 'SieveCertDefs.lean')):
        m = re.match(r'def (DEN|K) : ℕ := (.+)$', line)
        if m:
            got[m.group(1)] = power(m.group(2))
    return got['DEN'], got['K']


DEN, K = constants()


def num(s):
    """A coordinate of a cell: a numeral or `DEN / 2 + 1`."""
    s = s.strip()
    if s == 'DEN / 2 + 1':
        return DEN // 2 + 1
    return int(s)


def imports(path):
    """The modules that a Lean file imports, in order, that are files of lib/pnt."""
    out = []
    for line in lines(path):
        m = re.match(r'import (\S+)$', line)
        if m and os.path.exists(os.path.join(PNT, m.group(1) + '.lean')):
            out.append(m.group(1))
        elif line.startswith('namespace'):
            break
    return out


def statement(it, first):
    """The text of a theorem's statement from its first line up to `:=`, joined into one line."""
    text = first
    while ':=' not in text:
        text += ' ' + next(it).strip()
    return text[:text.index(':=')]


def chain(tag):
    """The root theorem `tree<tag>`: its floor, its top, its total and its pieces at the top level, in order."""
    main = os.path.join(PNT, 'Linnik%s.lean' % tag)
    it = lines(main)
    for line in it:
        if line.startswith('theorem tree%s :' % tag):
            head = statement(it, line)
            body = []
            for line in it:
                if not line.strip():
                    break
                body.append(line)
            break
    else:
        raise SystemExit('fig_cost: no theorem tree%s in %s' % (tag, main))
    m = re.fullmatch(r'theorem tree%s : PR \[\((\d+), (DEN / 2 \+ 1)\)\] false (\d+) ' % tag, head)
    if not m:
        raise SystemExit('fig_cost: tree%s has an unexpected statement: %s' % (tag, head))
    floor, top, total = int(m.group(1)), num(m.group(2)), int(m.group(3))
    text = ' '.join(s.strip() for s in body)
    if not (text.startswith('pr_mono (') and text.endswith('(by decide)')):
        raise SystemExit('fig_cost: tree%s is not pr_mono of a chain' % tag)
    pieces = re.findall(r'part%s (tree%s_\d+) \(by decide\)|\((node%s_\d+)\)|(node%s_\d+)\)'
                        % (tag, tag, tag, tag), text)
    names = [a or b or c for a, b, c in pieces]
    if text.count('pr_split') != len(names) - 1:
        raise SystemExit('fig_cost: tree%s: %d splits for %d pieces' % (tag, text.count('pr_split'), len(names)))
    return floor, top, total, names, ['Linnik%s' % tag] + imports(main)


def nodes(tag, want, mods):
    """The cells `node<tag>_i : PR [(a, b)] false c` named in `want`, from the modules `mods`."""
    got = {}
    pat = re.compile(r'theorem (node%s_\d+) : PR \[\((\d+), (\d+|DEN / 2 \+ 1)\)\] (true|false) (\d+) $' % tag)
    for mod in mods:
        if len(got) == len(want):
            break
        it = lines(os.path.join(PNT, mod + '.lean'))
        for line in it:
            if line.startswith('theorem node%s_' % tag) and line.split()[1] in want:
                s = statement(it, line)
                m = pat.fullmatch(s)
                if not m or m.group(4) != 'false':
                    raise SystemExit('fig_cost: %s is not a cell of the first prime: %s' % (line.split()[1], s))
                got[m.group(1)] = (num(m.group(2)), num(m.group(3)), int(m.group(5)), mod)
    return got


def parts(tag, want, mods):
    """The parts `tree<tag>_k : (partD solve<tag> TOP [] false [cuts] A K HINT).1 ≤ c` named in `want`."""
    got = {}
    pat = re.compile(r'theorem (tree%s_\d+) : \(partD solve%s (\d+) \[(.*?)\] (true|false) \[([\d,\s]*)\] (\d+)\s+'
                     r'K 0x[0-9a-f]+(?: … [0-9a-f]*)?\)\.1\s*≤ (\d+) ' % (tag, tag))
    for mod in mods:
        if len(got) == len(want):
            break
        it = lines(os.path.join(PNT, mod + '.lean'))
        for line in it:
            if line.startswith('theorem tree%s_' % tag) and line.split()[1] in want:
                s = statement(it, line)
                m = pat.fullmatch(s)
                if not m or m.group(3) or m.group(4) != 'false':
                    raise SystemExit('fig_cost: %s is not a part of the first prime: %s' % (line.split()[1], s[:300]))
                got[m.group(1)] = (int(m.group(6)), int(m.group(2)), int(m.group(7)), mod)
    return got


def exponent(tag, mods):
    """The route's exponent `L`, from `def route<tag> : Route := ⟨a / b, …⟩`."""
    for mod in mods:
        for line in lines(os.path.join(PNT, mod + '.lean')):
            m = re.search(r'def route%s : Route := ⟨(\d+) / (\d+),' % tag, line)
            if m:
                return Fr(int(m.group(1)), int(m.group(2)))
    raise SystemExit('fig_cost: no route%s' % tag)


def certificate(tag):
    """The pieces of `tree<tag>`, in order: (name, a, b, c), the range [a, b) in units of 1/DEN and the cost c in
    units of 1/K; with the floor, the top and the total. Asserts that the pieces tile [floor, top) and that their
    costs add up to the total."""
    floor, top, total, names, mods = chain(tag)
    cells = nodes(tag, {n for n in names if n.startswith('node')}, mods)
    prts = parts(tag, {n for n in names if n.startswith('tree')}, mods)
    pieces = []
    for n in names:
        src = cells.get(n) or prts.get(n)
        if src is None:
            raise SystemExit('fig_cost: %s not found in the modules that Linnik%s.lean imports' % (n, tag))
        pieces.append((n,) + src)
    at = floor
    for n, a, b, c, _ in pieces:
        if a != at or b <= a:
            raise SystemExit('fig_cost: %s: the piece [%d, %d) does not start at %d' % (n, a, b, at))
        if c >= K:
            raise SystemExit('fig_cost: %s: cost %d is not below K' % (n, c))
        at = b
    if at != top:
        raise SystemExit('fig_cost: tree%s: the pieces end at %d, not at %d' % (tag, at, top))
    s = sum(p[3] for p in pieces)
    if s != total:
        raise SystemExit('fig_cost: tree%s: the pieces cost %d, not the total %d' % (tag, s, total))
    return {'tag': tag, 'L': exponent(tag, mods), 'floor': floor, 'top': top, 'total': total, 'sum': s,
            'pieces': pieces}


def density(piece):
    """The cost per unit of the first prime's exponent on a piece: `(c/K)/((b − a)/DEN)`."""
    _, a, b, c, _ = piece
    return Fr(c, K) / Fr(b - a, DEN)


def area(cert, s, t):
    """The area under the step function on `[s, t]` (exponents), in units of `K`: the cost of the pieces inside, and
    the share of the pieces cut by `s` or `t` in proportion to their length."""
    out = Fr(0)
    for p in cert['pieces']:
        lo, hi = max(Fr(p[1], DEN), s), min(Fr(p[2], DEN), t)
        if hi > lo:
            out += density(p) * (hi - lo)
    return out


def median(cert):
    """The exponent below which the step function's area is half the total."""
    half, run = Fr(cert['total'], 2 * K), Fr(0)
    for p in cert['pieces']:
        w = Fr(p[2] - p[1], DEN)
        if run + density(p) * w >= half:
            return Fr(p[1], DEN) + (half - run) / density(p)
        run += density(p) * w


CUTS = [Fr(1, 5), Fr(3, 10), Fr(2, 5)]    # the ranges of the shares that `--table` prints


def table(certs):
    for cert in certs:
        print('L = %s: floor %d = %.7f, total %d = %.8f K, pieces %d, their sum %d (%s)' % (
            cert['L'], cert['floor'], cert['floor'] / DEN, cert['total'], cert['total'] / K, len(cert['pieces']),
            cert['sum'], 'equal' if cert['sum'] == cert['total'] else 'below by %d' % (cert['total'] - cert['sum'])))
        for p in cert['pieces']:
            n, a, b, c, mod = p
            print('  %-16s [%.6f, %.6f)  width %.6f  cost %.6f K  per unit %.4f   %s' % (
                n, a / DEN, b / DEN, (b - a) / DEN, c / K, float(density(p)), mod))
    print()
    print('The area under each curve on a range of the exponent, in units of K and as a share of the total:')
    ends = [None] + CUTS + [Fr(1, 2)]
    for cert in certs:
        tot = Fr(cert['total'], K)
        lo = Fr(cert['floor'], DEN)
        print('L = %s (total %.6f K)' % (cert['L'], float(tot)))
        for s, t in zip(ends, ends[1:]):
            s = lo if s is None else s
            a = area(cert, s, t)
            print('  [%.4f, %.4f]  %.4f K  %5.1f%%' % (s, t, float(a), float(100 * a / tot)))
        top = max(cert['pieces'], key=density)
        big = max(cert['pieces'], key=lambda p: p[3])
        print('  half of the cost lies above %.4f; the piece of largest cost per unit is [%.6f, %.6f), %.3f;'
              ' of largest cost [%.6f, %.6f), %.5f K' % (float(median(cert)), top[1] / DEN, top[2] / DEN,
                                                        float(density(top)), big[1] / DEN, big[2] / DEN, big[3] / K))


STYLE = {'21500': 'figblue, solid', '21000': 'figorange, dash pattern=on 3pt off 1.5pt'}


def dec(x, places):
    """A fraction as a decimal with `places` digits, rounded to nearest."""
    q = round(x * 10 ** places)
    sign = '-' if q < 0 else ''
    q = abs(q)
    return '%s%d.%0*d' % (sign, q // 10 ** places, places, q % 10 ** places)


def frac(x):
    """`L` as the paper writes it, `43/20`."""
    return '%d/%d' % (x.numerator, x.denominator)


def tikz(certs):
    """The text of fig-cost.tex."""
    # the axis stops above every piece but the last of each certificate; the two last pieces are cut there
    rest = max(density(p) for c in certs for p in c['pieces'][:-1])
    top = int(rest) + 1
    ends = [density(c['pieces'][-1]) for c in certs]
    if min(ends) <= top or len({(c['pieces'][-1][1], c['pieces'][-1][2]) for c in certs}) != 1:
        raise SystemExit('fig_cost: the last pieces are not one high spike on the same range')
    out = ['% Generated by tools/linnik/fig_cost.py; do not edit by hand.',
           '% The cost per unit of the first prime\'s exponent of the pieces of Linnik21500.tree21500 (43/20) and',
           '% Linnik21000.tree21000 (21/10); the area under each step function is the certificate\'s cost c/K.',
           r'\begin{tikzpicture}',
           r'\begin{axis}[',
           r'  width=12cm, height=7.4cm,',
           r'  xmin=0, xmax=0.5, ymin=0, ymax=%d,' % top,
           r'  axis lines=left, axis line style={figgray, line width=0.4pt, -},',
           r'  tick style={figgray, line width=0.4pt}, tick align=outside, major tick length=2pt,',
           r'  xtick={0, 0.1, 0.2, 0.3, 0.4, 0.5}, ytick={0, 2, ..., %d},' % (top // 2 * 2),
           r'  xticklabel style={/pgf/number format/fixed, /pgf/number format/precision=1},',
           r'  ticklabel style={font=\footnotesize},',
           r'  ymajorgrids, grid style={figgray!45, line width=0.3pt},',
           r'  xlabel={$\log p_1/\log x$},',
           r'  ylabel={cost$/\mathcal K$ per unit of $\log p_1/\log x$},',
           r'  label style={font=\small},',
           r'  clip=false,',
           r'  legend cell align=left,',
           r'  legend style={at={(axis cs:0.16,%d)}, anchor=north west, draw=none, fill=white,' % top,
           r'    font=\footnotesize, row sep=1pt},',
           r'  legend image post style={xscale=1.2},',
           r']',
           ]
    for cert in certs:
        pts = []
        for p in cert['pieces']:
            pts.append('(%s,%s)' % (dec(Fr(p[1], DEN), 6), dec(density(p), 4)))
        last = cert['pieces'][-1]
        pts[-1] = '(%s,%d)' % (dec(Fr(last[1], DEN), 6), top)       # cut at the top of the axis
        pts.append('(%s,%d)' % (dec(Fr(last[2], DEN), 6), top))
        out.append(r'\addplot[%s, line width=0.9pt, const plot mark left] coordinates {' % STYLE[cert['tag']])
        for i in range(0, len(pts), 6):
            out.append('  ' + ' '.join(pts[i:i + 6]))
        out.append('};')
        out.append(r'\addlegendentry{$L = %s$}' % frac(cert['L']))
    # the direct labels, with a thin leader to a point of each curve where the two are apart: Theorem 1.2's at the
    # top of its step below 0.26, Theorem 1.1's at the bottom of its dip above 0.45
    for cert in certs:
        if cert['tag'] == '21500':
            p = max((q for q in cert['pieces'] if Fr(1, 5) <= Fr(q[1], DEN) < Fr(13, 50)), key=density)
            at, move, anchor = density(p), '(-0.5cm,0.55cm)', 'south east'
        else:
            p = min((q for q in cert['pieces'] if Fr(q[1], DEN) >= Fr(9, 20)), key=density)
            at, move, anchor = density(p), '(-0.45cm,-0.3cm)', 'east'
        mid = Fr(p[1] + p[2], 2 * DEN)
        out.append(r'\draw[figgray, line width=0.3pt] (axis cs:%s,%s) -- ++%s' % (dec(mid, 6), dec(at, 4), move))
        out.append(r'  node[anchor=%s, inner sep=1.5pt, font=\footnotesize, text=black] {$L = %s$};'
                   % (anchor, frac(cert['L'])))
    # the two floors f_*/D, thin and gray, labelled at their tops
    heights = {'21500': Fr(top * 9, 20), '21000': Fr(top * 12, 20)}
    for cert in certs:
        f, h = Fr(cert['floor'], DEN), heights[cert['tag']]
        out.append(r'\draw[figgray, line width=0.35pt] (axis cs:%s,0) -- (axis cs:%s,%s)'
                   % (dec(f, 6), dec(f, 6), dec(h, 2)))
        out.append(r'  node[anchor=south west, inner sep=1.5pt, font=\footnotesize, text=black]'
                   r' {$f_*/D = %s$ at $%s$};' % (dec(f, 4), frac(cert['L'])))
    # the break mark on the two cut steps, and their heights
    last = certs[0]['pieces'][-1]
    x0, y0 = dec(Fr(last[1], DEN), 6), dec(Fr(top * 39, 40), 3)
    out.append(r'\fill[white] (axis cs:%s,%s) ++(-3pt,-2.5pt) -- ++(6pt,2pt) -- ++(0,3pt) -- ++(-6pt,-2pt) -- cycle;'
               % (x0, y0))
    out.append(r'\draw[black, line width=0.4pt] (axis cs:%s,%s) ++(-3pt,-2.5pt) -- ++(6pt,2pt)'
               r' ++(-6pt,1pt) -- ++(6pt,2pt);' % (x0, y0))
    out.append(r'\node[anchor=south east, inner sep=1.5pt, font=\footnotesize, text=black] at (axis cs:%s,%d)'
               % (x0, top))
    out.append(r'  {on $[%s, %s]$, above the scale: $%s$ at $%s$ and $%s$ at $%s$};' % (
        dec(Fr(last[1], DEN), 4), dec(Fr(last[2], DEN), 1),
        dec(ends[0], 2), frac(certs[0]['L']), dec(ends[1], 2), frac(certs[1]['L'])))
    out += [r'\end{axis}', r'\end{tikzpicture}', '']
    return '\n'.join(out)


def main():
    args = sys.argv[1:]
    certs = [certificate(t) for t in TAGS]
    if '--table' in args:
        table(certs)
        return
    text = tikz(certs)
    if '--check' in args:
        try:
            with open(OUT) as f:
                old = f.read()
        except FileNotFoundError:
            old = None
        if old != text:
            print('fig_cost: %s differs from what the script writes; run tools/linnik/fig_cost.py' %
                  os.path.relpath(OUT, ROOT))
            sys.exit(1)
        print('fig_cost: %s is up to date' % os.path.relpath(OUT, ROOT))
        return
    with open(OUT, 'w') as f:
        f.write(text)
    print('fig_cost: wrote %s' % os.path.relpath(OUT, ROOT))


if __name__ == '__main__':
    main()
