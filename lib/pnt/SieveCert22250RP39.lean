/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 406–416 of 5796

File 39 of 465: the parts `rows22250R_406` … `rows22250R_416` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 88041 tests: row 44 columns 44–359, row 45 columns 0–13, row 45 columns
14–16, row 45 columns 17–19, row 45 columns 20–22, row 45 columns 23–24, row 45 columns 25–26, row 45 columns 27–27,
row 45 columns 28–28, row 45 columns 29–29, row 45 columns 30–30), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_406 : rowsJ2 44 45 44 360 ≤ 59797310397 := by decide +kernel

theorem rows22250R_407 : rowsJ2 45 46 0 14 ≤ 913220207048 := by decide +kernel

theorem rows22250R_408 : rowsJ2 45 46 14 17 ≤ 1717754959573 := by decide +kernel

theorem rows22250R_409 : rowsJ2 45 46 17 20 ≤ 2034911273564 := by decide +kernel

theorem rows22250R_410 : rowsJ2 45 46 20 23 ≤ 1808939097334 := by decide +kernel

theorem rows22250R_411 : rowsJ2 45 46 23 25 ≤ 979514745391 := by decide +kernel

theorem rows22250R_412 : rowsJ2 45 46 25 27 ≤ 797556555913 := by decide +kernel

theorem rows22250R_413 : rowsJ2 45 46 27 28 ≤ 338009078736 := by decide +kernel

theorem rows22250R_414 : rowsJ2 45 46 28 29 ≤ 302924649786 := by decide +kernel

theorem rows22250R_415 : rowsJ2 45 46 29 30 ≤ 277940156010 := by decide +kernel

theorem rows22250R_416 : rowsJ2 45 46 30 31 ≤ 260576816893 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_406
#print axioms SieveCert.rows22250R_416
