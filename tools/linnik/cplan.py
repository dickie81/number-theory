"""The planner in C (`cplan/hint_plan.c`, `hint_cert.py --cplan`): the parameters file from the Python planner's
own constants, the program run on cells of the first prime, and its plans read back as the Python planner's tuples.
The C planner is the Python planner's search (`Planner.plan`, the lazy hints' `resolve` and the replan of
`row_job`), method by method; `--cplan` changes how long a plan takes and how much memory it needs, not what it is
(`cplan_test.py` compares the two). The program is compiled once for each version of its sources, in the temporary
directory, with `$CC` (`cc` if unset); it needs a C compiler with `__int128` (GCC or Clang) and libm."""
import hashlib
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
import res_test as rt  # noqa: E402
import mirror8 as m8  # noqa: E402

SRCS = [os.path.join(HERE, 'cplan', f) for f in ('hint_plan.c', 'num.h', 'res.h')]


def build():
    """The compiled planner, built once for each version of the sources."""
    tag = hashlib.sha256(b''.join(open(f, 'rb').read() for f in SRCS)).hexdigest()[:16]
    exe = os.path.join(tempfile.gettempdir(), f'hint_plan_{tag}')
    if not os.path.exists(exe):
        tmp = f'{exe}.{os.getpid()}'
        subprocess.run([os.environ.get('CC', 'cc'), '-O3', '-std=gnu11', '-ffp-contract=off', '-fno-fast-math', '-o',
                        tmp, SRCS[0], '-lm'], check=True)
        os.replace(tmp, exe)
    return exe


def _f(x):
    return float(x).hex()


def params(par_):
    """The parameters file's text for the certificate's parameters `par_` (a `hint_cert.Par`)."""
    # the module that defines `par_`'s class: `__main__` when hint_cert.py runs as a script, whose `SEC` its
    # `planner()` sets (a fresh `import hint_cert` would have the default table)
    hc = sys.modules[type(par_).__module__]
    P = par_.planner()
    T = P.T
    assert P.res_frozen in (True, False) and P.res_cof in (True, False), 'measurement modes are not supported'
    assert P.blk == 1 and P.blkF == 1 and not P.split2 and not P.rev, 'blk, split2 and rev are not supported'
    lam = P.lamK
    assert float(lam) == lam, 'the price of a second is not a float'
    out = []

    def kv(k, v):
        out.append(f'{k} {v}')
    kv('version', 1)
    for k, v in (('DEN', tc.DEN), ('K', tc.K), ('BIG', tc.BIG), ('CAPK', rc.CAPK), ('Ln', T.Ln), ('Ld', T.Ld),
                 ('hI', P.hI), ('hF', P.hF), ('hR', P.hR), ('hQ', P.hQ), ('wmin', P.wmin), ('kappa', P.kappa),
                 ('depth', P.depth), ('depthR', P.depthR), ('depthF', P.depthF), ('maxlen', P.maxlen),
                 ('fuel', P.fuel), ('pos', int(P.pos)), ('skip', P.skip), ('skipmin', P.skipmin),
                 ('energy', int(T.energy)), ('res', int(bool(P.res))), ('resF', int(bool(P.res_frozen))),
                 ('cof', int(bool(P.res_cof))), ('lv', int(bool(P.res_lv))), ('lazy', int(bool(P.res_lazy))),
                 ('rmerge', int(bool(P.res_merge))), ('split', int(P.res_split)), ('ycorner', int(bool(P.res_y))),
                 ('exh', int(P.exh)), ('split2', int(P.split2)), ('blk', P.blk), ('blkF', P.blkF),
                 ('redo', int(bool(P.redo))), ('merge', int(bool(P.merge)))):
        kv(k, int(v))
    kv('lamK', _f(lam))
    kv('dm0', P.dmerge[0])
    kv('dm1', P.dmerge[1])
    for k in 'VEDRBFPS':
        for z in (0, 1):
            v = hc.SEC.get((k, bool(z)))
            kv(f'SEC{k}{z}', 'none' if v is None else _f(v))
    kv('nleaf', len(tc.LEAFXR))
    for l, r in tc.LEAFXR:
        out.append(' '.join(str(x) for x in l + r))
    kv('TOPK', m8.TOPK)
    kv('W1K', m8.W1K)
    kv('LD', m8.LD)
    out.append(' '.join(str(x) for x in m8.LNT))
    assert len(m8.LNT) == 17
    for k, v in (('rDEN', rt.DEN), ('NP', rt.NP), ('PK', rt.PK), ('GB', rt.GB), ('EB', rt.EB), ('SH', rt.SH),
                 ('LVKS', rt.LVKS), ('S', rt.S)):
        kv(k, v)
    kv('nFT', len(rt.FT))
    for lst in (rt.FT, rt.FTM, rt.IA, rt.DH):
        assert len(lst) == rt.NP + 1
        out.append(' '.join(str(x) for x in lst))
    for k in ('WC', 'MG', 'K1U', 'K1D', 'M1U', 'M1D', 'HP', 'LVE', 'OFF', 'E23', 'C310', 'C15U', 'C15D', 'C65D', 'C43',
              'W2'):
        kv(k, getattr(rt, k))
    ck = [rt.fl(t) for t in rt.TOPS] + [rt.fl(A * (1 - hi)) for lo, hi, A in rt.HUX]
    kv('nCK', len(ck))
    out.append(' '.join(str(x) for x in ck))
    kv('nHF', len(rt._HF))
    for (lo, hi, A), t in zip(rt._HF, rt._TF):
        out.append(' '.join(_f(x) for x in (lo, hi, A, t)))
    kv('CHI', _f(rt._CHI))
    kv('LVEQ', _f(float(rt.LVEQ)))
    for k in ('restLo', 'restHi', 'uC0', 'uA', 'uB', 'uC', 'vA', 'vB', 'vC', 'umC0', 'umA', 'D1max', 'T5', 'T6', 'T5E',
              'u3', 'fmax3'):
        kv(k, getattr(P, k))
    kv('fillLo', T.fillLo)
    out.append('end')
    return '\n'.join(out) + '\n'


def parse_tree(toks, i):
    """The node in prefix order at `toks[i]`, and the index after it."""
    stack, root = [], None
    while True:
        t = toks[i]
        if t in ('V', 'E', 'D'):
            node, i = (t,), i + 1
        elif t == 'R':
            node, i = ('R', int(toks[i + 1]), int(toks[i + 2]), int(toks[i + 3], 16)), i + 4
        elif t == 'Y':
            node, i = ('R', int(toks[i + 1]), 'Y', int(toks[i + 2], 16)), i + 3
        elif t in ('B', 'F', 'P'):
            sel, nk, bits = int(toks[i + 1]), int(toks[i + 2]), toks[i + 3]
            node = (t, sel, [], [] if bits == '-' else [int(ch) for ch in bits])
            i += 4
            stack.append([node, nk])
            if nk:
                continue
            stack.pop()
        elif t == 'S':
            node = ['S']
            i += 1
            stack.append([node, 2])
            continue
        else:
            raise ValueError(f'a malformed plan at token {i}: {t!r}')
        # attach the finished node to its parent, closing the parents it completes
        while True:
            if not stack:
                return node, i
            par, left = stack[-1]
            if isinstance(par, list):
                par.append(node)
            else:
                par[2].append(node)
            stack[-1][1] -= 1
            if stack[-1][1]:
                break
            stack.pop()
            node = tuple(par) if isinstance(par, list) else par


def parse(text):
    """The plans in the program's output: a list of `(a, b, cost, calls, fcalls, stat, node)`."""
    out = []
    lines = iter(text.split('\n'))
    for line in lines:
        if not line:
            continue
        assert line.startswith('CELL '), line[:80]
        a, b = map(int, line.split()[1:3])
        c = int(next(lines).split()[1])
        calls, fcalls = map(int, next(lines).split()[1:3])
        st = next(lines).split()[1:]
        stat = {st[j]: int(st[j + 1]) for j in range(0, len(st), 2)}
        toks = next(lines).split()
        assert toks[0] == 'TREE'
        node, i = parse_tree(toks, 1)
        assert i == len(toks), 'tokens after the plan'
        assert next(lines) == 'END'
        out.append((a, b, c, calls, fcalls, stat, node))
    return out


def params_file(par_):
    """The parameters file of `par_`, written once in the temporary directory (named by its content)."""
    text = params(par_)
    path = os.path.join(tempfile.gettempdir(), f'cplan-{hashlib.sha1(text.encode()).hexdigest()[:16]}.txt')
    if not os.path.exists(path):
        tmp = f'{path}.{os.getpid()}'
        with open(tmp, 'w') as fh:
            fh.write(text)
        os.replace(tmp, path)
    return path


def plan_cells(par_, cells):
    """The plans of the cells `(a, b)` of the first prime, in the program's output order."""
    exe = build()
    path = params_file(par_)
    inp = ''.join(f'{a} {b}\n' for a, b in cells)
    r = subprocess.run([exe, path], input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f'hint_plan failed ({r.returncode}): {r.stderr.strip()}')
    return parse(r.stdout)
