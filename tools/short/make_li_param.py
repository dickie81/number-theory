"""Rebuild li_param.inc and li_tuples.h from R. Li's arXiv ancillary file LB_521_160_1.cpp (arXiv:2308.04458v8).

li521_orig.inc is his code up to the integration routines, unchanged but for line endings (for val_orig.cpp).
li_param.inc is the same code with theta a parameter TH, gamma(theta) a parameter
GAMMA (set by the harness from his Lemma 4.1), nu(alpha) computed from its definition, and his three Type-II_n
predicates renamed Li{3,4,5}DL722 so that the harness can wrap them. li_tuples.h lists the (middle deltas, last delta)
of the Hoelder tuples inside those predicates.

Usage: python3 -I make_li_param.py LB_521_160_1.cpp OUTDIR"""
import os
import re
import sys


def sub(text, old, new, count):
    """Replace old by new, checking that it occurs exactly count times."""
    n = text.count(old)
    assert n == count, f"expected {count} of {old!r}, found {n}"
    return text.replace(old, new)


lines = open(sys.argv[1], newline='').read().replace('\r\n', '\n').split('\n')
end = lines.index('// Trapezoidal rule for 1D integration') - 1
assert lines[end] == '' and lines[end - 1] == '}'
text = '\n'.join(lines[:end]) + '\n'
open(os.path.join(sys.argv[2], 'li521_orig.inc'), 'w').write(text)  # unmodified, for val_orig.cpp

old_nu = text[text.index('bool belowNu(double t1, double t2) {\n'):]
old_nu = old_nu[:old_nu.index('\n}\n') + 3]
text = sub(text, old_nu, """bool belowNu(double t1, double t2) {
    // nu(alpha) = min(2(theta - alpha)/(2h - 1), gamma) for alpha in I_h = [1/2 - 2h(theta - 1/2), 1/2 - (2h - 2)(theta - 1/2))
    if (t1 < 2 * TH - 1 || t1 >= 0.5) return false;
    int h = (int)std::floor((0.5 - t1) / (2 * (TH - 0.5))) + 1;
    double nu = std::min(2 * (TH - t1) / (2 * h - 1), GAMMA);
    return t2 < std::min(t1, nu);
}
""", 1)
text = sub(text, 'return (std::abs(t1 - t2) < 0.042 && t1 + t2 > 1 - ((44.0 * 0.521 - 21.0)/23) );',
           'return (std::abs(t1 - t2) < 2 * TH - 1 && t1 + t2 > 1 - GAMMA);', 1)
text = sub(text, 'double theta0 = 0.042;', 'double theta0 = (2 * TH - 1);', 8)
for d, args in ((3, 't1, t2, t3'), (4, 't1, t2, t3, t4'), (5, 't1, t2, t3, t4, t5')):
    sig = ', '.join('double ' + a for a in args.split(', '))
    text = sub(text, f'bool AsymptoticRegion{d}DL722({sig}) {{', f'bool Li{d}DL722({sig}) {{', 1)
assert '0.042' not in text
text = text.replace('0.521', 'TH')
text = sub(text, 'using namespace std;\n', """using namespace std;
double TH = 0.521, GAMMA = 0;
bool AsymptoticRegion3DL722(double, double, double);
bool AsymptoticRegion4DL722(double, double, double, double);
bool AsymptoticRegion5DL722(double, double, double, double, double);
""", 1)
open(os.path.join(sys.argv[2], 'li_param.inc'), 'w').write(text)

# Hoelder tuples: a disjunct "(t1) >= 1 - TH && (t2) >= (1 - TH)/a && ... && (rest) >= (2 * (1 - TH))/b" uses the
# moment 2a on each middle factor and b + 1 on the last; the other disjuncts are left to Li's predicate.
out = []
for d in (3, 4, 5):
    body = text[text.index(f'bool Li{d}DL722('):]
    body = body[:body.index('\n}\n')]
    mids, lasts = [], []
    for disj in re.split(r'\|\|', body):
        a = re.findall(r'\(t\d\) >= \(1 - TH\)/(\d+)', disj)
        b = re.findall(r'>= \(2 \* +\(1 - TH\)\)/(\d+)', disj)
        if '(t1) >= 1 - TH' in disj and len(a) == d - 1 and len(b) == 1 and '<=' not in disj and '2 * (t' not in disj:
            mids.append([2 * int(x) for x in a])
            lasts.append(int(b[0]) + 1)
    rows = ','.join('{' + ','.join(map(str, m)) + '}' for m in mids)
    out.append(f'// Li{d}DL722: (middle deltas, last delta)\n'
               f'static const int T{d}_N = {len(mids)};\n'
               f'static const int T{d}_MID[{len(mids)}][{d - 1}] = {{{rows}}};\n'
               f'static const int T{d}_LAST[{len(mids)}] = {{{",".join(map(str, lasts))}}};\n')
open(os.path.join(sys.argv[2], 'li_tuples.h'), 'w').write(''.join(out))
