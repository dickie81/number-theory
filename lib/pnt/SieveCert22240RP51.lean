/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 508–514 of 5066

File 51 of 387: the parts `rows22240R_508` … `rows22240R_514` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 90479 in units of a depth-4 test: row 48 columns 38–38, row 48 columns
39–39, row 48 columns 40–40, row 48 columns 41–41, row 48 columns 42–42, row 48 columns 43–43, row 48 columns
44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_508 : rowsJ2 48 49 38 39 ≤ 52725167103 := by decide +kernel

theorem rows22240R_509 : rowsJ2 48 49 39 40 ≤ 36141000242 := by decide +kernel

theorem rows22240R_510 : rowsJ2 48 49 40 41 ≤ 25828458864 := by decide +kernel

theorem rows22240R_511 : rowsJ2 48 49 41 42 ≤ 14920889274 := by decide +kernel

theorem rows22240R_512 : rowsJ2 48 49 42 43 ≤ 10326904066 := by decide +kernel

theorem rows22240R_513 : rowsJ2 48 49 43 44 ≤ 5098862454 := by decide +kernel

theorem rows22240R_514 : rowsJ2 48 49 44 45 ≤ 83309569895 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_508
#print axioms SieveCert.rows22240R_514
