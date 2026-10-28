/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3367–3381 of 4715

File 261 of 351: the parts `rows22250R_3367` … `rows22250R_3381` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96365 in units of a depth-4 test: row 126 columns 82–85, row 126
columns 86–88, row 126 columns 89–93, row 126 columns 94–339, row 127 columns 0–24, row 127 columns 25–28, row 127
columns 29–35, row 127 columns 36–54, row 127 columns 55–57, row 127 columns 58–59, row 127 columns 60–60, row 127
columns 61–61, row 127 columns 62–62, row 127 columns 63–63, row 127 columns 64–64), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3367 : rowsJ2 126 127 82 86 ≤ 7360465977072 := by decide +kernel

theorem rows22250R_3368 : rowsJ2 126 127 86 89 ≤ 16425939839369 := by decide +kernel

theorem rows22250R_3369 : rowsJ2 126 127 89 94 ≤ 218094011739142 := by decide +kernel

theorem rows22250R_3370 : rowsJ2 126 127 94 340 ≤ 707387918715707 := by decide +kernel

theorem rows22250R_3371 : rowsJ2 127 128 0 25 ≤ 4129373074327 := by decide +kernel

theorem rows22250R_3372 : rowsJ2 127 128 25 29 ≤ 16509241449071 := by decide +kernel

theorem rows22250R_3373 : rowsJ2 127 128 29 36 ≤ 11108121289524 := by decide +kernel

theorem rows22250R_3374 : rowsJ2 127 128 36 55 ≤ 3058729309522 := by decide +kernel

theorem rows22250R_3375 : rowsJ2 127 128 55 58 ≤ 5902724892898 := by decide +kernel

theorem rows22250R_3376 : rowsJ2 127 128 58 60 ≤ 6486719604818 := by decide +kernel

theorem rows22250R_3377 : rowsJ2 127 128 60 61 ≤ 4115718731518 := by decide +kernel

theorem rows22250R_3378 : rowsJ2 127 128 61 62 ≤ 4655174864313 := by decide +kernel

theorem rows22250R_3379 : rowsJ2 127 128 62 63 ≤ 5123443313183 := by decide +kernel

theorem rows22250R_3380 : rowsJ2 127 128 63 64 ≤ 5542454804181 := by decide +kernel

theorem rows22250R_3381 : rowsJ2 127 128 64 65 ≤ 5888996930501 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3367
#print axioms SieveCert.rows22250R_3381
