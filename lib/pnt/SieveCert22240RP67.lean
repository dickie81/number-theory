/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 658–666 of 5066

File 67 of 387: the parts `rows22240R_658` … `rows22240R_666` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 95938 in units of a depth-4 test: row 53 columns 35–35, row 53 columns
36–36, row 53 columns 37–37, row 53 columns 38–38, row 53 columns 39–39, row 53 columns 40–40, row 53 columns 41–41,
row 53 columns 42–42, row 53 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_658 : rowsJ2 53 54 35 36 ≤ 17078645054 := by decide +kernel

theorem rows22240R_659 : rowsJ2 53 54 36 37 ≤ 8006051325 := by decide +kernel

theorem rows22240R_660 : rowsJ2 53 54 37 38 ≤ 3997121389 := by decide +kernel

theorem rows22240R_661 : rowsJ2 53 54 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_662 : rowsJ2 53 54 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_663 : rowsJ2 53 54 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_664 : rowsJ2 53 54 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_665 : rowsJ2 53 54 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_666 : rowsJ2 53 54 43 44 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_658
#print axioms SieveCert.rows22240R_666
