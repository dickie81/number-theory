"""The planner in C (`cplan/hint_plan.c`, `hint_cert.py --cplan`): the parameters file from the Python planner's
own constants, the program run on cells of the first prime, and its plans read back as the Python planner's tuples.
The C planner is the Python planner's search (`Planner.plan`, the lazy hints' `resolve` and the replan of
`row_job`), method by method; `--cplan` changes how long a plan takes and how much memory it needs, not what it is
(`cplan_test.py` compares the two). The same program is the generator in C (`cplan/gen.h`, `hint_cert.py --cgen`):
the cut of a heavy cell into parts (`cut`, in the run that plans it, or from a plan given), the parts of light cells
(`add_part`) and the transcoding of a part's hints for `Par.hl` (`hl_parts`), with the hints of each part written and
checked by the kernel's mirror (`dHints`, `dPart`) as the Python generator does (`cgen_test.py` compares the two);
and the plan of a heavy cell kept in a cache, read back from its parts' hints, cut again (`recut_cells`).
The program is compiled once for each version of its sources, in the temporary directory, with `$CC` (`cc` if
unset); it needs a C compiler with `__int128` (GCC or Clang) and libm."""
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

SRCS = [os.path.join(HERE, 'cplan', f) for f in ('hint_plan.c', 'num.h', 'res.h', 'gen.h')]


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
    assert P.blk == 1 and P.blkF == 1 and not P.rev, 'blk and rev are not supported'
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
    # the generator's (`--cgen`): the window's lines named by the hints, and `cut`'s limits
    assert P.res_hl in (True, False), 'measurement modes are not supported'
    kv('hl', int(P.res_hl))
    kv('cap', _f(par_.cap))
    kv('levels', int(par_.levels))
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


def dump_tree(node, out):
    """The tokens of the plan `node` as the program writes them (`parse_tree`'s input), appended to `out`."""
    stack = [node]
    while stack:
        x = stack.pop()
        k = x[0]
        if k in ('V', 'E', 'D'):
            out.append(k)
        elif k == 'R':
            assert x[2] not in (-1, -2), 'a window\'s leaf without its hint'
            out.append(f'Y {x[1]} {x[3]:x}' if x[2] == 'Y' else f'R {x[1]} {x[2]} {x[3]:x}')
        elif k in ('B', 'F', 'P'):
            out.append(f'{k} {x[1]} {len(x[2])} {"".join("1" if b else "0" for b in x[3]) or "-"}')
            stack.extend(reversed(x[2]))
        elif k == 'S':
            out.append('S')
            stack.append(x[2])
            stack.append(x[1])
        else:
            raise ValueError(k)
    return out


def parse_part(toks, i):
    """A part as the program writes it (`PART …`): `add_part`'s tuple, and the index after it."""
    assert toks[i] == 'PART', toks[i]
    top, nbl = int(toks[i + 1]), int(toks[i + 2])
    i += 3
    bl = [(int(toks[i + 2 * j]), int(toks[i + 2 * j + 1])) for j in range(nbl)]
    i += 2 * nbl
    par, ncs = toks[i] == '1', int(toks[i + 1])
    i += 2
    cs = [int(x) for x in toks[i:i + ncs]]
    i += ncs
    a, c, secs_, steps, ncnt = int(toks[i]), int(toks[i + 1]), float.fromhex(toks[i + 2]), int(toks[i + 3]), \
        int(toks[i + 4])
    i += 5
    cnt = {}
    for _ in range(ncnt):
        cnt[(toks[i], toks[i + 1] == '1')] = int(toks[i + 2])
        i += 3
    h = int(toks[i], 16)
    return (top, bl, par, cs, a, c, h, secs_, steps, cnt), i + 1


def parse_piece(toks, i, parts):
    """A piece of a cut cell (`p i` or `b …`) as `hint_cert.cut` returns it, its parts' indices those of the cell's
    own list `parts`, and the index after it."""
    if toks[i] == 'p':
        return ('part', int(toks[i + 1])), i + 2
    assert toks[i] == 'b', toks[i]
    nbl = int(toks[i + 1])
    i += 2
    bl = [(int(toks[i + 2 * j]), int(toks[i + 2 * j + 1])) for j in range(nbl)]
    i += 2 * nbl
    par, f = toks[i] == '1', int(toks[i + 1])
    cfg = (int(toks[i + 2]), int(toks[i + 3]), int(toks[i + 4]), int(toks[i + 5]), toks[i + 6] == '1')
    nout = int(toks[i + 7])
    i += 8
    out = []
    for _ in range(nout):
        p, i = parse_piece(toks, i, parts)
        out.append(p)
    cost = sum(parts[p[1]][5] if p[0] == 'part' else p[6] for p in out)
    return ('buch', bl, par, f, cfg, out, cost), i


def parse_cut(lines):
    """A heavy cell's parts and pieces (`PARTS m`, the parts, `PIECE …`) from the iterator of lines `lines`."""
    head = next(lines).split()
    assert head[0] == 'PARTS', head[:2]
    parts = []
    for _ in range(int(head[1])):
        p, _ = parse_part(next(lines).split(), 0)
        parts.append(p)
    toks = next(lines).split()
    assert toks[0] == 'PIECE'
    piece, i = parse_piece(toks, 1, parts)
    assert i == len(toks)
    return piece, parts


def parse(text):
    """The plans in the program's output: a list of `(a, b, cost, calls, fcalls, stat, node)`; with `cut`, a heavy
    cell has in place of its plan `node` the triple `(counts, piece, parts)` of its plan's steps and its cut."""
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
        if toks[0] == 'COUNT':
            cnt = {(toks[j], toks[j + 1] == '1'): int(toks[j + 2]) for j in range(1, len(toks), 3)}
            piece, parts = parse_cut(lines)
            node = (cnt, piece, parts)
        else:
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


def plan_cells(par_, cells, cut=False):
    """The plans of the cells `(a, b)` of the first prime, in the program's output order; with `cut`, a heavy cell
    (`row_job`'s test) is cut into its parts by the generator in C (`parse`)."""
    exe = build()
    path = params_file(par_)
    inp = ''.join(f'{a} {b}\n' for a, b in cells)
    r = subprocess.run([exe, path] + (['cut'] if cut else []), input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f'hint_plan failed ({r.returncode}): {r.stderr.strip()}')
    return parse(r.stdout)


# the generator in C (`--cgen`): `hint_cert.add_part`, `cut` and `hl_parts` with the same results

def _gen(par_, cmds):
    exe = build()
    path = params_file(par_)
    r = subprocess.run([exe, path, 'gen'], input='\n'.join(cmds) + '\n', capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f'hint_plan gen failed ({r.returncode}): {r.stderr.strip()}')
    return r.stdout


def add_parts(par_, groups):
    """`hint_cert.add_part` of each group `(bl, par, [(lo, hi, plan)])`: the parts' tuples, in order."""
    cmds = []
    for bl, par, group in groups:
        toks = ['ADD', str(int(par)), str(len(bl))] + [f'{x} {y}' for x, y in bl] + [str(len(group))]
        for lo, hi, node in group:
            toks.append(f'{lo} {hi}')
            dump_tree(node, toks)
        cmds.append(' '.join(toks))
    out = []
    for line in _gen(par_, cmds).split('\n'):
        if line:
            p, i = parse_part(line.split(), 0)
            out.append(p)
    assert len(out) == len(groups)
    return out


def cut_cells(par_, cells):
    """`hint_cert.cut` of the heavy cells `(a, b, plan)` of the first prime: `(piece, parts)` for each."""
    cmds = []
    for a, b, node in cells:
        cmds.append(' '.join(dump_tree(node, ['CUT', str(a), str(b)])))
    lines = iter(_gen(par_, cmds).split('\n'))
    out = [parse_cut(lines) for _ in cells]
    assert not ''.join(lines)
    return out


def dump_piece(p, out):
    """The tokens of a piece of a cut cell (`parse_piece`'s input), appended to `out`."""
    if p[0] == 'part':
        out += ['p', str(p[1])]
        return out
    _, bl, par, f, cfg, ps, _ = p
    out += ['b', str(len(bl))] + [f'{x} {y}' for x, y in bl] + [str(int(par)), str(f)]
    out += [str(int(v)) for v in cfg[:4]] + [str(int(bool(cfg[4]))), str(len(ps))]
    for q in ps:
        dump_piece(q, out)
    return out


def _entry_cmd(cmd, r):
    """The command `RECUT` or `REBUILD` of a heavy cell kept in a cache: `r` = ('heavy', a, b, piece, parts, info)."""
    _, a, b, piece, parts = r[:5]
    toks = [cmd, str(a), str(b), str(len(parts))]
    for top, bl, par, cs, a_, c, h in (p[:7] for p in parts):
        toks += (['P', str(top), str(len(bl))] + [f'{x} {y}' for x, y in bl] + [str(int(par)), str(len(cs))]
                 + [str(x) for x in cs] + [str(a_), str(c), f'{h:x}'])
    toks.append('PIECE')
    return ' '.join(dump_piece(piece, toks))


def recut_cells(par_, entries):
    """The heavy cells kept in a cache (`row_job`'s `('heavy', a, b, piece, parts, info)`, cut without the halves of
    a split cell) cut again by `cut`: each cell's plan is read back from its parts' hints by the kernel's search
    (`gen.h`, `rebuild`), the steps of its pieces above them, and cut as `hint_cert.cut` cuts it now; the entries
    with their new pieces and parts, the rest as it was (the same plan, cost and counts)."""
    if not entries:
        return []
    lines = iter(_gen(par_, [_entry_cmd('RECUT', r) for r in entries]).split('\n'))
    out = []
    for r in entries:
        piece, parts = parse_cut(lines)
        assert piece[6] == r[3][6], 'the cell cut again at another cost'
        out.append(r[:3] + (piece, parts) + r[5:])
    return out


def rebuild_trees(par_, entries):
    """The plans of heavy cells kept in a cache, read back from their parts' hints (`recut_cells`), as trees."""
    out = []
    for line in _gen(par_, [_entry_cmd('REBUILD', r) for r in entries]).split('\n'):
        if line:
            toks = line.split()
            assert toks[0] == 'TREE'
            node, i = parse_tree(toks, 1)
            assert i == len(toks)
            out.append(node)
    assert len(out) == len(entries)
    return out


def hl_parts(par_, parts):
    """`hint_cert.hl_parts`: each part as it is if its hints pass with the window's lines named (`Par.hl`), else
    with its hints transcoded (`transcode_hl`)."""
    cmds = []
    for top, bl, par, cs, a, c, h in (p[:7] for p in parts):
        cmds.append(' '.join(['HL', str(top), str(len(bl))] + [f'{x} {y}' for x, y in bl]
                             + [str(int(par)), str(len(cs))] + [str(x) for x in cs] + [str(a), str(c), f'{h:x}']))
    out = []
    lines = [x for x in _gen(par_, cmds).split('\n') if x]
    assert len(lines) == len(parts)
    for p, line in zip(parts, lines):
        t = line.split()
        assert t[0] == 'HLPART'
        out.append(p if t[1] == '0' else p[:6] + (int(t[2], 16),) + p[7:])
    return out
