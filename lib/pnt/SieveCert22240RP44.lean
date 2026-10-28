/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 453–458 of 5066

File 44 of 387: the parts `rows22240R_453` … `rows22240R_458` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 94222 in units of a depth-4 test: row 46 columns 36–36, row 46 columns
37–37, row 46 columns 38–38, row 46 columns 39–39, row 46 columns 40–40, row 46 columns 41–41), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_453 : rowsJ2 46 47 36 37 ≤ 155406747515 := by decide +kernel

theorem rows22240R_454 : rowsJ2 46 47 37 38 ≤ 126089617992 := by decide +kernel

theorem rows22240R_455 : rowsJ2 46 47 38 39 ≤ 104440128121 := by decide +kernel

theorem rows22240R_456 : rowsJ2 46 47 39 40 ≤ 80146078069 := by decide +kernel

theorem rows22240R_457 : rowsJ2 46 47 40 41 ≤ 63533096228 := by decide +kernel

theorem rows22240R_458 : rowsJ2 46 47 41 42 ≤ 44906920997 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_453
#print axioms SieveCert.rows22240R_458
