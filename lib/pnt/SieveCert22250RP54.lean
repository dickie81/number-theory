/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 548–560 of 4715

File 54 of 351: the parts `rows22250R_548` … `rows22250R_560` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96497 tests: row 50 columns 45–45, row 50 columns 46–46, row 50 columns
47–47, row 50 columns 48–48, row 50 columns 49–49, row 50 columns 50–339, row 51 columns 0–14, row 51 columns 15–19,
row 51 columns 20–22, row 51 columns 23–24, row 51 columns 25–25, row 51 columns 26–26, row 51 columns 27–27), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_548 : rowsJ2 50 51 45 46 ≤ 298464184838 := by decide +kernel

theorem rows22250R_549 : rowsJ2 50 51 46 47 ≤ 890422730916 := by decide +kernel

theorem rows22250R_550 : rowsJ2 50 51 47 48 ≤ 1768241424576 := by decide +kernel

theorem rows22250R_551 : rowsJ2 50 51 48 49 ≤ 2612841441122 := by decide +kernel

theorem rows22250R_552 : rowsJ2 50 51 49 50 ≤ 3573835731070 := by decide +kernel

theorem rows22250R_553 : rowsJ2 50 51 50 340 ≤ 4800979041495 := by decide +kernel

theorem rows22250R_554 : rowsJ2 51 52 0 15 ≤ 2753147255721 := by decide +kernel

theorem rows22250R_555 : rowsJ2 51 52 15 20 ≤ 2151077577106 := by decide +kernel

theorem rows22250R_556 : rowsJ2 51 52 20 23 ≤ 772197956812 := by decide +kernel

theorem rows22250R_557 : rowsJ2 51 52 23 25 ≤ 346924863990 := by decide +kernel

theorem rows22250R_558 : rowsJ2 51 52 25 26 ≤ 134411004441 := by decide +kernel

theorem rows22250R_559 : rowsJ2 51 52 26 27 ≤ 115106542282 := by decide +kernel

theorem rows22250R_560 : rowsJ2 51 52 27 28 ≤ 98484763760 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_548
#print axioms SieveCert.rows22250R_560
