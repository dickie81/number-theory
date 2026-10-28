/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 602–613 of 4715

File 59 of 351: the parts `rows22250R_602` … `rows22250R_613` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 93496 in units of a depth-4 test: row 52 columns 38–38, row 52 columns
39–39, row 52 columns 40–40, row 52 columns 41–41, row 52 columns 42–42, row 52 columns 43–43, row 52 columns 44–44,
row 52 columns 45–45, row 52 columns 46–46, row 52 columns 47–47, row 52 columns 48–48, row 52 columns 49–49), each
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

theorem rows22250R_602 : rowsJ2 52 53 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_603 : rowsJ2 52 53 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_604 : rowsJ2 52 53 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_605 : rowsJ2 52 53 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_606 : rowsJ2 52 53 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_607 : rowsJ2 52 53 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_608 : rowsJ2 52 53 44 45 ≤ 74506086041 := by decide +kernel

theorem rows22250R_609 : rowsJ2 52 53 45 46 ≤ 292436562584 := by decide +kernel

theorem rows22250R_610 : rowsJ2 52 53 46 47 ≤ 872440232041 := by decide +kernel

theorem rows22250R_611 : rowsJ2 52 53 47 48 ≤ 1732530971186 := by decide +kernel

theorem rows22250R_612 : rowsJ2 52 53 48 49 ≤ 2560073899764 := by decide +kernel

theorem rows22250R_613 : rowsJ2 52 53 49 50 ≤ 3501660465564 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_602
#print axioms SieveCert.rows22250R_613
