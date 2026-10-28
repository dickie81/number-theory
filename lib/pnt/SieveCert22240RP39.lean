/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 410–421 of 5066

File 39 of 387: the parts `rows22240R_410` … `rows22240R_421` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 91169 in units of a depth-4 test: row 44 columns 44–339, row 45 columns
0–13, row 45 columns 14–16, row 45 columns 17–19, row 45 columns 20–22, row 45 columns 23–24, row 45 columns 25–25,
row 45 columns 26–26, row 45 columns 27–27, row 45 columns 28–28, row 45 columns 29–29, row 45 columns 30–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_410 : rowsJ2 44 45 44 340 ≤ 42416069813 := by decide +kernel

theorem rows22240R_411 : rowsJ2 45 46 0 14 ≤ 1149262671618 := by decide +kernel

theorem rows22240R_412 : rowsJ2 45 46 14 17 ≤ 2160098408658 := by decide +kernel

theorem rows22240R_413 : rowsJ2 45 46 17 20 ≤ 2560368586057 := by decide +kernel

theorem rows22240R_414 : rowsJ2 45 46 20 23 ≤ 2277937881230 := by decide +kernel

theorem rows22240R_415 : rowsJ2 45 46 23 25 ≤ 1234260367787 := by decide +kernel

theorem rows22240R_416 : rowsJ2 45 46 25 26 ≤ 530316062993 := by decide +kernel

theorem rows22240R_417 : rowsJ2 45 46 26 27 ≤ 475930497174 := by decide +kernel

theorem rows22240R_418 : rowsJ2 45 46 27 28 ≤ 430065645914 := by decide +kernel

theorem rows22240R_419 : rowsJ2 45 46 28 29 ≤ 390759178215 := by decide +kernel

theorem rows22240R_420 : rowsJ2 45 46 29 30 ≤ 366006903662 := by decide +kernel

theorem rows22240R_421 : rowsJ2 45 46 30 31 ≤ 355348129924 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_410
#print axioms SieveCert.rows22240R_421
