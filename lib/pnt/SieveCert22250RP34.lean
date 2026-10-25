/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 361–371 of 4715

File 34 of 351: the parts `rows22250R_361` … `rows22250R_371` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 90588 tests: row 43 columns 42–42, row 43 columns 43–339, row 44 columns
0–13, row 44 columns 14–17, row 44 columns 18–20, row 44 columns 21–23, row 44 columns 24–25, row 44 columns 26–26,
row 44 columns 27–27, row 44 columns 28–28, row 44 columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_361 : rowsJ2 43 44 42 43 ≤ 29308803977 := by decide +kernel

theorem rows22250R_362 : rowsJ2 43 44 43 340 ≤ 20541219284 := by decide +kernel

theorem rows22250R_363 : rowsJ2 44 45 0 14 ≤ 1731742940844 := by decide +kernel

theorem rows22250R_364 : rowsJ2 44 45 14 18 ≤ 2983278854959 := by decide +kernel

theorem rows22250R_365 : rowsJ2 44 45 18 21 ≤ 2098356640716 := by decide +kernel

theorem rows22250R_366 : rowsJ2 44 45 21 24 ≤ 1606296252257 := by decide +kernel

theorem rows22250R_367 : rowsJ2 44 45 24 26 ≤ 800986154802 := by decide +kernel

theorem rows22250R_368 : rowsJ2 44 45 26 27 ≤ 333768529424 := by decide +kernel

theorem rows22250R_369 : rowsJ2 44 45 27 28 ≤ 299487949799 := by decide +kernel

theorem rows22250R_370 : rowsJ2 44 45 28 29 ≤ 276501562303 := by decide +kernel

theorem rows22250R_371 : rowsJ2 44 45 29 30 ≤ 273893433165 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_361
#print axioms SieveCert.rows22250R_371
