/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 508–515 of 4715

File 50 of 351: the parts `rows22250R_508` … `rows22250R_515` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 90986 in units of a depth-4 test: row 49 columns 34–34, row 49 columns
35–35, row 49 columns 36–36, row 49 columns 37–37, row 49 columns 38–38, row 49 columns 39–39, row 49 columns 40–40,
row 49 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_508 : rowsJ2 49 50 34 35 ≤ 28342418716 := by decide +kernel

theorem rows22250R_509 : rowsJ2 49 50 35 36 ≤ 16921732535 := by decide +kernel

theorem rows22250R_510 : rowsJ2 49 50 36 37 ≤ 9890161172 := by decide +kernel

theorem rows22250R_511 : rowsJ2 49 50 37 38 ≤ 4793209685 := by decide +kernel

theorem rows22250R_512 : rowsJ2 49 50 38 39 ≤ 4122400064 := by decide +kernel

theorem rows22250R_513 : rowsJ2 49 50 39 40 ≤ 3439390602 := by decide +kernel

theorem rows22250R_514 : rowsJ2 49 50 40 41 ≤ 2763538363 := by decide +kernel

theorem rows22250R_515 : rowsJ2 49 50 41 42 ≤ 2074140010 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_508
#print axioms SieveCert.rows22250R_515
