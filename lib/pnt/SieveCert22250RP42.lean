/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 428–435 of 5796

File 42 of 465: the parts `rows22250R_428` … `rows22250R_435` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 96572 tests: row 45 columns 42–42, row 45 columns 43–43, row 45 columns
44–44, row 45 columns 45–359, row 46 columns 0–13, row 46 columns 14–17, row 46 columns 18–20, row 46 columns
21–23), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_428 : rowsJ2 45 46 42 43 ≤ 66232299567 := by decide +kernel

theorem rows22250R_429 : rowsJ2 45 46 43 44 ≤ 52930704207 := by decide +kernel

theorem rows22250R_430 : rowsJ2 45 46 44 45 ≤ 39715410429 := by decide +kernel

theorem rows22250R_431 : rowsJ2 45 46 45 360 ≤ 30976284137 := by decide +kernel

theorem rows22250R_432 : rowsJ2 46 47 0 14 ≤ 1001639962202 := by decide +kernel

theorem rows22250R_433 : rowsJ2 46 47 14 18 ≤ 2350526640321 := by decide +kernel

theorem rows22250R_434 : rowsJ2 46 47 18 21 ≤ 1874431390670 := by decide +kernel

theorem rows22250R_435 : rowsJ2 46 47 21 24 ≤ 1540796066592 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_428
#print axioms SieveCert.rows22250R_435
