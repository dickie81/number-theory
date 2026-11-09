#!/usr/bin/env python3
"""The certificate files of the fifth located zero of the Davenport–Heilbronn function, `lib/dh/DHLocate5Cert*.lean`.

    python3 scripts/gen_dh_locate5.py            # write the files
    python3 scripts/gen_dh_locate5.py --check    # compare them with the ones in lib/dh

The zero is near `c = 918601/1000000 + (2441547865/100000) i`. `lib/dh/DHBallDefs.lean` defines a fixed-point
evaluator (`DHBall.run`) for the sums over `n < 30000` of `n^{-c}` and `log n · n^{-c}`, by residue class mod 5, and
`lib/dh/DHBall.lean` proves that it encloses them. This script repeats the evaluator's integer arithmetic exactly and
writes the states after each fifty blocks:

    DHLocate5States.lean       the six states `st1, …, st6`, after each thousand blocks
    DHLocate5Cert{0..5}.lean   `run (1000 i) 1000 st_i = st_{i+1}`, in twenty kernel computations of fifty blocks each
                               (`decide +kernel`), through intermediate states

The kernel recomputes every state, so nothing here is trusted: a wrong state makes its file fail to compile.
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = 2 ** 80
TWO_PI = (7595904947272677161581685, 12091)
RE_N, RE_D = 918601, 1000000
IM_N, IM_D = 2441547865, 100000
EXP_REM = 14857800560707
BLOCKS, CHUNK, SUB = 6000, 1000, 50


def b_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def b_sub(a, b):
    return (a[0] - b[0], a[1] + b[1])


def b_neg(a):
    return (-a[0], a[1])


def b_mul(a, b):
    return (a[0] * b[0] // S, (abs(a[0]) * b[1] + abs(b[0]) * a[1] + a[1] * b[1]) // S + 2)


def b_div_nat(a, k):
    return (a[0] // k, a[1] // k + 2)


def b_mul_rat(a, p, q):
    return (a[0] * p // q, a[1] * p // q + 2)


def c_add(a, b):
    return (b_add(a[0], b[0]), b_add(a[1], b[1]))


def c_sub(a, b):
    return (b_sub(a[0], b[0]), b_sub(a[1], b[1]))


def c_mul(a, b):
    return (b_sub(b_mul(a[0], b[0]), b_mul(a[1], b[1])), b_add(b_mul(a[0], b[1]), b_mul(a[1], b[0])))


def c_div_nat(a, k):
    return (b_div_nat(a[0], k), b_div_nat(a[1], k))


def c_smul(l, a):
    return (b_mul(l, a[0]), b_mul(l, a[1]))


ONE = ((S, 0), (0, 0))
ZERO = ((0, 0), (0, 0))


def exp_loop(v, m, fuel, term, total):
    while fuel:
        term, total = c_div_nat(c_mul(term, v), m + 1), c_add(total, term)
        m, fuel = m + 1, fuel - 1
    return total


def sq_loop(j, z):
    for _ in range(j):
        z = c_mul(z, z)
    return z


def red_arg(L):
    y = b_mul_rat(L, IM_N, IM_D)
    k = (2 * y[0] + TWO_PI[0]) // (2 * TWO_PI[0])
    th = (y[0] - k * TWO_PI[0], y[1] + abs(k) * TWO_PI[1])
    return (b_div_nat(b_neg(b_mul_rat(L, RE_N, RE_D)), 16), b_div_nat(b_neg(th), 16))


def exp_ball(v):
    if (abs(v[0][0]) + v[0][1]) ** 2 + (abs(v[1][0]) + v[1][1]) ** 2 <= S ** 2:
        p = exp_loop(v, 0, 14, ONE, ZERO)
        return sq_loop(4, ((p[0][0], p[0][1] + EXP_REM), (p[1][0], p[1][1] + EXP_REM)))
    return ((0, S), (0, S))


def term(L):
    return exp_ball(red_arg(L))


def log_terms(n):
    return 64 if n < 16 else 16 if n < 256 else 8 if n < 4096 else 6


def log_step(n):
    N, n1, p, acc = log_terms(n), n + 1, 1, 0
    for i in range(N):
        p *= n1
        acc += S // p // (i + 1)
    return (acc + N, N + S // ((n + 1) ** N * n) + 1)


def up(L, T):
    return (abs(L[0]) + L[1]) ** 2 * (abs(T[0][0]) + T[0][1] + abs(T[1][0]) + T[1][1]) // (S * S) + 1


def step(m, st):
    L1, A, B, A1, B1, d2a, d2b = st
    T1 = term(L1)
    L2 = b_add(L1, log_step(5 * m + 1))
    T2 = term(L2)
    L3 = b_add(L2, log_step(5 * m + 2))
    T3 = term(L3)
    L4 = b_add(L3, log_step(5 * m + 3))
    T4 = term(L4)
    L5 = b_add(L4, log_step(5 * m + 4))
    return (b_add(L5, log_step(5 * m + 5)),
            c_sub(c_add(A, T1), T4),
            c_sub(c_add(B, T2), T3),
            c_add(c_sub(A1, c_smul(L1, T1)), c_smul(L4, T4)),
            c_add(c_sub(B1, c_smul(L2, T2)), c_smul(L3, T3)),
            d2a + up(L1, T1) + up(L4, T4),
            d2b + up(L2, T2) + up(L3, T3))


INIT = ((0, 0), ZERO, ZERO, ZERO, ZERO, 0, 0)


def states():
    """The states after each `SUB` blocks."""
    out, st = [], INIT
    for m in range(BLOCKS):
        st = step(m, st)
        if (m + 1) % SUB == 0:
            out.append(st)
    return out


def lean_b(b):
    return f"⟨{b[0]}, {b[1]}⟩"


def lean_cb(z):
    return f"⟨{lean_b(z[0])}, {lean_b(z[1])}⟩"


def lean_st(st):
    L, A, B, A1, B1, d2a, d2b = st
    return (f"  ⟨{lean_b(L)},\n    {lean_cb(A)},\n    {lean_cb(B)},\n    {lean_cb(A1)},\n    {lean_cb(B1)},\n"
            f"    {d2a},\n    {d2b}⟩")


def files():
    sts = states()
    per = CHUNK // SUB                      # steps in a file
    nfiles = BLOCKS // CHUNK
    out = {}
    body = ["import DHBallDefs", "",
            "/-!",
            "# The fifth located zero of the Davenport–Heilbronn function: the states of the evaluator",
            "",
            f"`st{{i}}` is the state of `DHBall.run` after the blocks `0, …, {CHUNK}·i − 1`. Written by",
            "`scripts/gen_dh_locate5.py`; `DHLocate5Cert0`, …, `DHLocate5Cert5` have the kernel recompute each from the one",
            "before.",
            "-/", "", "namespace DHBall", ""]
    for i in range(1, nfiles + 1):
        body += [f"/-- The state after the blocks `0, …, {CHUNK * i - 1}`. -/", f"def st{i} : St :=",
                 lean_st(sts[per * i - 1]), ""]
    body += ["end DHBall", ""]
    out["DHLocate5States.lean"] = "\n".join(body)
    for i in range(nfiles):
        first = "init" if i == 0 else f"st{i}"
        lines = ["import DHLocate5States", "",
                 "/-!",
                 f"# The fifth located zero: the blocks `{CHUNK * i}, …, {CHUNK * (i + 1) - 1}`",
                 "",
                 f"`run_{i}`: these blocks take `{first}` to `st{i + 1}`. The kernel computes them {SUB} at a time (`decide +kernel`),",
                 f"through the intermediate states `mid_{i}_k`, so that no single computation needs much memory. Written by",
                 "`scripts/gen_dh_locate5.py`.",
                 "-/", "", "namespace DHBall", ""]
        names = [first] + [f"mid_{i}_{k}" for k in range(1, per)] + [f"st{i + 1}"]
        for k in range(1, per):
            lines += [f"/-- The state after the blocks `0, …, {CHUNK * i + SUB * k - 1}`. -/", f"def mid_{i}_{k} : St :=",
                      lean_st(sts[per * i + k - 1]), ""]
        for k in range(per):
            a = CHUNK * i + SUB * k
            lines += [f"theorem step_{i}_{k} : run {a} {SUB} {names[k]} = {names[k + 1]} := by decide +kernel", ""]
        lines += [f"/-- The blocks `{CHUNK * i}, …, {CHUNK * (i + 1) - 1}` take `{first}` to `st{i + 1}`. -/",
                  f"theorem run_{i} : run {CHUNK * i} {CHUNK} {first} = st{i + 1} := by",
                  f"  have h := step_{i}_0"]
        lines += [f"  have h := run_trans h step_{i}_{k}" for k in range(1, per)]
        lines += ["  exact h", "", "end DHBall", ""]
        out[f"DHLocate5Cert{i}.lean"] = "\n".join(lines)
    return out


def main():
    check = "--check" in sys.argv
    bad = 0
    for name, text in files().items():
        path = os.path.join(ROOT, "lib", "dh", name)
        if check:
            if not os.path.exists(path) or open(path, encoding="utf-8").read() != text:
                print(f"{name}: differs from the generator's")
                bad += 1
        else:
            open(path, "w", encoding="utf-8").write(text)
            print(f"wrote lib/dh/{name}")
    if check:
        print("the certificate files of the fifth zero are the generator's" if not bad else "DH LOCATE 5 CERT FAIL")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
