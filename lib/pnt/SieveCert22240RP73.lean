/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 720–727 of 5066

File 73 of 387: the parts `rows22240R_720` … `rows22240R_727` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 91458 in units of a depth-4 test: row 55 columns 30–30, row 55 columns
31–31, row 55 columns 32–32, row 55 columns 33–33, row 55 columns 34–34, row 55 columns 35–35, row 55 columns 36–36,
row 55 columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_720 : rowsJ2 55 56 30 31 ≤ 51303273892 := by decide +kernel

theorem rows22240R_721 : rowsJ2 55 56 31 32 ≤ 38173790183 := by decide +kernel

theorem rows22240R_722 : rowsJ2 55 56 32 33 ≤ 25136651037 := by decide +kernel

theorem rows22240R_723 : rowsJ2 55 56 33 34 ≤ 16566608142 := by decide +kernel

theorem rows22240R_724 : rowsJ2 55 56 34 35 ≤ 8043172910 := by decide +kernel

theorem rows22240R_725 : rowsJ2 55 56 35 36 ≤ 4014464263 := by decide +kernel

theorem rows22240R_726 : rowsJ2 55 56 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_727 : rowsJ2 55 56 37 38 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_720
#print axioms SieveCert.rows22240R_727
