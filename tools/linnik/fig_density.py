#!/usr/bin/env python3
"""fig_density.py [--check] [--table]: the figure of the density exponents in the Linnik paper.

The figure, `papers/linnik-exponent/fig-density.tex`, plots against `σ` on `[1/2, 1]` the density exponent
`g(σ)/(1 − σ)` of the paper's two density curves, as staircases: on each of its steps a curve is `A(1 − σ)`, so its
exponent is the constant `A` there.

* `g_H` (`SieveCurveHx.ghx`, 18 pieces), solid: the trivial count `1` below `β† = 7789/10000`, Huxley's steps above,
  `(101/50)(1 − σ)` from `5/6` on. Below `β†` its exponent `1/(1 − σ)` leaves the plot at its top edge, where an
  arrow tip marks the cut; a label says so and gives the exponent's value at `β†`, computed from the Lean's `β†`. A
  short dotted drop with an arrow tip at `β†` shows where `g_H` comes back, on its first step.
* `g*` (`SieveCurve7D.g7d`, 67 pieces), dashed: the trivial count below `4/7` (exponent `1/(1 − σ)`, at most `7/3`),
  twenty Ingham steps up to `5/7`, thirty steps of Chen, Gupta and Li's Proposition 3.1 up to `131/168`, and `g_H`
  from there on.

Both curves are read from the Lean sources in `lib/pnt` by `route_limits.parse`, in exact rationals; the last piece,
which `parse` stops at `11/12`, is drawn on to `1`, as the Lean defines it. Behind them, thin and gray, are the
classical exponents as the paper states them: Ingham's `3/(2 − σ)` on `[1/2, 3/4]`, Huxley's `3/(3σ − 1)` on
`[3/4, 5/6]` (it is below `2` beyond, off the plot), Chen, Gupta and Li's `4/(1 + σ)` on `[5/7, 4/5]` (the paper
states it on `[7/10, 4/5]`; below `5/7` it exceeds `7/3`, and Ingham's exponent is the one used there); the two
levels where the classical argument stops, `12/5` at `σ = 3/4` and `7/3` at `σ = 5/7`; and the strip `σ > 11/12`,
where Input 1 leaves no zero. The numbers typed in here are the plot's window, the places of the labels, these
formulas and their meeting points `3/4` and `5/7`, and `11/12`. The ticks `4/7`, `β†` and `5/6`, every point of the two
curves and the value printed at `β†` come from the Lean; the literals `7789/10000`, `131/168` and the like appear only
in the checks. The script checks the figure's numbers: the two classical maxima, that `4/(1 + σ)` meets Huxley's
exponent at `7/9`, below `β†`, that each step lies at or above the classical exponent it rounds, that `g_H = g*` from
`131/168` on, and the largest step of `g*`; and that every plotted point lies inside the axis, so that nothing is
clipped.

The coordinates are computed exactly and printed with six decimals. `main.tex` inputs the file in a `figure`
environment and its preamble loads `pgfplots` (`compat=1.16`, the `fillbetween` library), the TikZ library
`patterns`, and the colours `figblue`, `figorange` and `figgray`.

Usage:
  fig_density.py           write `papers/linnik-exponent/fig-density.tex`
  fig_density.py --check   write nothing: regenerate the file in memory and compare it with the one on disk
                           (exit 1 on a difference)
  fig_density.py --table   print the pieces of the two curves and the figure's reference points

Needs Python 3 only. Under a second.
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

OUT = os.path.join(HERE, '..', '..', 'papers', 'linnik-exponent', 'fig-density.tex')

# The plot's window. The bottom edge is below Ingham's exponent at 1/2, which is 2; the top edge leaves room for the
# labels above 12/5.
X0, X1 = Fr(1, 2), Fr(1)
Y0, Y1 = Fr(197, 100), Fr(51, 20)
HALF_PLANE = Fr(11, 12)
DROP = Fr(23, 10)  # the top of the dotted drop at β†, below the label of Huxley's exponent


# The classical exponents, as the paper states them (Sections 1 and 2, and "What the inputs give without the sieve").
def ingham(s):
    return Fr(3) / (2 - s)


def huxley(s):
    return Fr(3) / (3 * s - 1)


def cgl(s):
    return Fr(4) / (1 + s)


def trivial(s):
    return 1 / (1 - s)


def need(ok, msg):
    if not ok:
        raise SystemExit(f'fig_density.py: {msg}')


def d6(x):
    """`x` rounded to six decimals, as a string (exact rounding of the fraction)."""
    n = round(Fr(x) * 10 ** 6)
    sign, n = ('-' if n < 0 else ''), abs(n)
    return f'{sign}{n // 10 ** 6}.{n % 10 ** 6:06d}'


def d2(x):
    """`x` rounded to two decimals, as a string."""
    return d6(round(Fr(x) * 100) / Fr(100))[:-4]


def curves():
    """The pieces `(lo, hi, A)` of `g_H` and `g*` from the Lean (`A = None` for the count `1`), the last one to `1`."""
    out = {}
    for name in ('ghx', 'g7d'):
        p = rl.parse(name)
        lo, hi, A = p[-1]
        need((hi, A) == (HALF_PLANE, Fr(101, 50)), f'the last piece of {name} is not (101/50)(1 − σ) up to 11/12')
        out[name] = p[:-1] + [(lo, X1, A)]
    return out['ghx'], out['g7d']


def check(gh, gs):
    """The statements of the figure and its caption, checked on the data."""
    beta = gh[1][0]
    need(beta == Fr(7789, 10000), f'β† is {beta}, not 7789/10000')
    need(gs[1][0] == Fr(4, 7) and gh[-1][0] == Fr(5, 6), 'g* does not start its steps at 4/7, or g_H its last piece at 5/6')
    need(len(gh) == 18 and len(gs) == 67, f'g_H has {len(gh)} pieces and g* {len(gs)}, not 18 and 67')
    need(gh[0] == (X0, beta, None), 'g_H is not the count 1 on [1/2, 7789/10000)')
    need(gs[0] == (X0, Fr(4, 7), None), 'g* is not the count 1 on [1/2, 4/7)')
    need(all(A is not None for _, _, A in gh[1:] + gs[1:]), 'a piece after the first is the count 1')
    i = gs.index(gh[2])
    need(gs[i:] == gh[2:] and gs[i][0] == Fr(131, 168), 'g* is not g_H from 131/168 on')
    need(gh[1][:2] == (beta, Fr(131, 168)), 'the first step of g_H is not [7789/10000, 131/168)')
    # each step lies at or above the classical exponent it rounds, over the whole step
    for lo, hi, A in gs[1:]:
        if hi <= Fr(5, 7):
            need(A >= ingham(hi), f'the step [{lo}, {hi}) of g* is below Ingham')
        elif hi <= Fr(131, 168):
            need(A >= cgl(lo), f'the step [{lo}, {hi}) of g* is below 4/(1 + σ)')
    for lo, hi, A in gh[1:]:
        if hi <= Fr(5, 6):
            need(A >= huxley(lo), f'the step [{lo}, {hi}) of g_H is below Huxley')
    # the classical maxima and the meeting points the figure marks
    need(ingham(Fr(3, 4)) == huxley(Fr(3, 4)) == Fr(12, 5), 'Ingham and Huxley do not meet at 12/5 at 3/4')
    need(ingham(Fr(5, 7)) == cgl(Fr(5, 7)) == Fr(7, 3), 'Ingham and 4/(1 + σ) do not meet at 7/3 at 5/7')
    need(huxley(Fr(5, 6)) == 2, 'Huxley is not 2 at 5/6')
    need(cgl(Fr(7, 9)) == huxley(Fr(7, 9)) and Fr(7, 9) < beta, '4/(1 + σ) does not meet Huxley at 7/9, below β†')
    need(trivial(Fr(4, 7)) == Fr(7, 3), 'the trivial exponent is not 7/3 at 4/7')
    top = max(A for _, _, A in gs[1:])
    need(top == Fr(11667, 5000) and gs[21] == (Fr(5, 7), Fr(1201, 1680), top), "g*'s largest step is not 2.3334 at 5/7")
    need(Fr(7, 3) < top < Fr(12, 5), "g*'s largest step is not between 7/3 and 12/5")
    return beta


def polyline(f, lo, hi, n):
    return [(lo + (hi - lo) * k / n, f(lo + (hi - lo) * k / n)) for k in range(n + 1)]


def stairs(pieces, start):
    """The points of a staircase from the piece `start` on: each step flat, a vertical line at each jump."""
    pts = []
    for lo, hi, A in pieces[start:]:
        pts += [(lo, A), (hi, A)]
    return pts


def coords(pts):
    for x, y in pts:
        need(X0 <= x <= X1 and Y0 <= y <= Y1, f'the point ({float(x)}, {float(y)}) is outside the axis')
    out, line = [], '    '
    for x, y in pts:
        c = f'({d6(x)},{d6(y)}) '
        if len(line) + len(c) > 118:
            out.append(line.rstrip())
            line = '    '
        line += c
    out.append(line.rstrip())
    return '\n'.join(out)


def plot(style, pts, legend=None):
    tail = f'\n  \\addlegendentry{{{legend}}}' if legend else ''
    return f'  \\addplot[{style}] coordinates {{\n{coords(pts)}\n  }};{tail}\n'


def tex(gh, gs, beta):
    exit_ = 1 - 1 / Y1  # where 1/(1 − σ) reaches the top edge
    xs = [X0, gs[1][0], Fr(5, 7), Fr(3, 4), beta, gh[-1][0], HALF_PLANE, X1]
    xl = ['1/2', '4/7', '5/7', '3/4', '\\beta^\\dagger', '5/6', '11/12', '1']
    ys = [Fr(2), Fr(21, 10), Fr(11, 5), Fr(7, 3), Fr(12, 5)]
    yl = ['2', '2.1', '2.2', '7/3', '12/5']
    p = []
    p.append('% Generated by tools/linnik/fig_density.py; do not edit by hand.\n')
    p.append('% The density exponents g(σ)/(1 − σ) of the curves g_H (SieveCurveHx.ghx) and g* (SieveCurve7D.g7d),\n'
             '% read from lib/pnt, against the classical exponents of Ingham, Huxley and Chen, Gupta and Li.\n')
    p.append('\\begin{tikzpicture}\n')
    p.append('\\begin{axis}[\n'
             '  scale only axis, width=10.4cm, height=6.8cm, axis on top,\n'
             f'  xmin={d6(X0)}, xmax={d6(X1)}, ymin={d6(Y0)}, ymax={d6(Y1)},\n'
             '  axis lines=left, axis line style={-, line width=0.4pt},\n'
             '  tick style={line width=0.4pt, black}, tick align=outside, major tick length=2pt,\n'
             f'  xtick={{{",".join(d6(x) for x in xs)}}},\n'
             f'  xticklabels={{{",".join("$" + s + "$" for s in xl)}}},\n'
             f'  ytick={{{",".join(d6(y) for y in ys)}}},\n'
             f'  yticklabels={{{",".join("$" + s + "$" for s in yl)}}},\n'
             '  tick label style={font=\\footnotesize}, label style={font=\\small},\n'
             '  xlabel={$\\sigma$}, ylabel={exponent $g(\\sigma)/(1 - \\sigma)$},\n'
             '  clip=false,\n'
             '  legend cell align=left,\n'
             '  legend style={draw=none, fill=white, font=\\footnotesize, at={(axis cs:0.503,2.547)}, anchor=north west,\n'
             '    row sep=-1pt, inner sep=2pt},\n'
             '  legend image post style={xscale=0.8},\n'
             ']\n')
    # the strip without zeros, hatched lightly
    p.append(f'  \\fill[pattern=north east lines, pattern color=figgray!45] (axis cs:{d6(HALF_PLANE)},{d6(Y0)})'
             f' rectangle (axis cs:{d6(X1)},{d6(Y1)});\n')
    p.append(f'  \\node[font=\\footnotesize, fill=white, inner sep=1.5pt, align=center] at (axis cs:{d6((HALF_PLANE + X1) / 2)},2.29)'
             ' {no zeros\\\\(Input~\\ref{inp:half-plane})};\n')
    # guide lines to the two classical maxima
    g = 'figgray, line width=0.3pt'
    p.append(f'  \\draw[{g}] (axis cs:{d6(X0)},{d6(Fr(12, 5))}) -- (axis cs:{d6(Fr(3, 4))},{d6(Fr(12, 5))})'
             f' -- (axis cs:{d6(Fr(3, 4))},{d6(Y0)});\n')
    p.append(f'  \\draw[{g}] (axis cs:{d6(X0)},{d6(Fr(7, 3))}) -- (axis cs:{d6(Fr(5, 7))},{d6(Fr(7, 3))})'
             f' -- (axis cs:{d6(Fr(5, 7))},{d6(Y0)});\n')
    # the classical exponents
    c = 'figgray, line width=0.4pt, forget plot'
    p.append(plot(c, polyline(ingham, X0, Fr(3, 4), 40)))
    p.append(plot(c, polyline(huxley, Fr(3, 4), Fr(5, 6), 40)))
    p.append(plot(c, polyline(cgl, Fr(5, 7), Fr(4, 5), 40)))
    # the two curves of the Lean: g_H solid blue (under), g* dashed orange (over)
    hs = 'figblue, line width=0.9pt, line join=round'
    p.append(plot(hs + ', forget plot, -stealth', polyline(trivial, X0, exit_, 24)))
    p.append(plot(hs, stairs(gh, 1), '$g_{\\mathrm H}$'))
    # where g_H comes back at β†: a short dotted drop onto its first step (the jump from 1/(1 − β†) is off the plot)
    p.append(f'  \\draw[figblue, line width=0.7pt, densely dotted, -stealth] (axis cs:{d6(beta)},{d6(DROP)})'
             f' -- (axis cs:{d6(beta)},{d6(gh[1][2])});\n')
    ss = 'figorange, line width=0.9pt, dash pattern=on 3pt off 1.6pt, line join=round'
    p.append(plot(ss, polyline(trivial, X0, Fr(4, 7), 12) + stairs(gs, 1), '$g^*$'))
    # the two maxima
    for x, y in ((Fr(3, 4), Fr(12, 5)), (Fr(5, 7), Fr(7, 3))):
        p.append(f'  \\fill[black] (axis cs:{d6(x)},{d6(y)}) circle[radius=1.3pt];\n')
    # labels: black for the data and the marks, figgray for the classical exponents
    lab = '  \\node[font=\\footnotesize, inner sep=1pt, {a}] at (axis cs:{x},{y}) {{{t}}};\n'
    p.append(lab.format(a='anchor=west, xshift=2pt', x=d6(Fr(3, 4)), y=d6(Fr(12, 5)), t='largest with Huxley'))
    p.append(lab.format(a='anchor=south east, xshift=-2pt, yshift=1pt, align=right', x=d6(Fr(5, 7)), y=d6(Fr(7, 3)),
                        t='largest with\\\\Chen, Gupta, Li'))
    p.append(lab.format(a='anchor=north west, align=left', x=d6(exit_ + Fr(1, 100)), y=d6(Y1),
                        t='$g_{\\mathrm H} = 1$ below $\\beta^\\dagger$: exponent\\\\$1/(1-\\sigma)$, '
                        f'${d2(trivial(beta))}$ at $\\beta^\\dagger$'))
    p.append(lab.format(a='anchor=south', x='0.605', y='2.205', t='$g^*$'))
    gl = 'text=figgray'
    p.append(lab.format(a='anchor=north west, ' + gl, x='0.535', y='2.05', t='Ingham $3/(2-\\sigma)$'))
    p.append(lab.format(a='anchor=west, xshift=1pt, ' + gl, x=d6(Fr(4, 5)), y=d6(cgl(Fr(4, 5))),
                        t='$4/(1+\\sigma)$'))
    p.append(lab.format(a='anchor=west, xshift=2pt, ' + gl, x=d6(Fr(3, 4) + Fr(1, 100)), y=d6(huxley(Fr(3, 4) + Fr(1, 100))),
                        t='Huxley $3/(3\\sigma-1)$'))
    p.append('\\end{axis}\n')
    p.append('\\end{tikzpicture}\n')
    return ''.join(p)


def table(gh, gs, beta):
    for name, pcs in (('g_H (SieveCurveHx.ghx)', gh), ('g* (SieveCurve7D.g7d)', gs)):
        print(f'{name}: {len(pcs)} pieces')
        for lo, hi, A in pcs:
            if A is None:
                print(f'  [{lo}, {hi})  count 1, exponent 1/(1 - σ) from {d6(trivial(lo))} to {d6(trivial(hi))}')
            else:
                print(f'  [{lo}, {hi})  A = {A} = {d6(A)}')
    print('reference: Ingham = Huxley = 12/5 at 3/4; Ingham = 4/(1 + σ) = 7/3 at 5/7; '
          f'1/(1 - σ) = {d6(trivial(beta))} at β† = {beta}; the half-plane at 11/12')


def main():
    gh, gs = curves()
    beta = check(gh, gs)
    if '--table' in sys.argv:
        table(gh, gs, beta)
        return 0
    txt = tex(gh, gs, beta)
    if '--check' in sys.argv:
        same = os.path.exists(OUT) and open(OUT, encoding='utf-8').read() == txt
        print('fig-density.tex', 'MATCHES the Lean' if same else 'DIFFERS from what the Lean gives: run fig_density.py')
        return 0 if same else 1
    with open(OUT, 'w', encoding='utf-8') as f:
        f.write(txt)
    print('wrote papers/linnik-exponent/fig-density.tex')
    return 0


if __name__ == '__main__':
    sys.exit(main())
