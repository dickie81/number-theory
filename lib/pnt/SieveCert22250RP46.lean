/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 455–465 of 5796

File 46 of 465: the parts `rows22250R_455` … `rows22250R_465` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 96539 tests: row 46 columns 44–44, row 46 columns 45–45, row 46 columns
46–359, row 47 columns 0–13, row 47 columns 14–17, row 47 columns 18–20, row 47 columns 21–23, row 47 columns 24–25,
row 47 columns 26–26, row 47 columns 27–27, row 47 columns 28–28), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_455 : rowsJ2 46 47 44 45 ≤ 25884960390 := by decide +kernel

theorem rows22250R_456 : rowsJ2 46 47 45 46 ≤ 17183827385 := by decide +kernel

theorem rows22250R_457 : rowsJ2 46 47 46 360 ≤ 14732613241 := by decide +kernel

theorem rows22250R_458 : rowsJ2 47 48 0 14 ≤ 1089574917622 := by decide +kernel

theorem rows22250R_459 : rowsJ2 47 48 14 18 ≤ 2293333909114 := by decide +kernel

theorem rows22250R_460 : rowsJ2 47 48 18 21 ≤ 1745010561091 := by decide +kernel

theorem rows22250R_461 : rowsJ2 47 48 21 24 ≤ 1406657490142 := by decide +kernel

theorem rows22250R_462 : rowsJ2 47 48 24 26 ≤ 718977407999 := by decide +kernel

theorem rows22250R_463 : rowsJ2 47 48 26 27 ≤ 301161665142 := by decide +kernel

theorem rows22250R_464 : rowsJ2 47 48 27 28 ≤ 267323613070 := by decide +kernel

theorem rows22250R_465 : rowsJ2 47 48 28 29 ≤ 237129725439 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_455
#print axioms SieveCert.rows22250R_465
