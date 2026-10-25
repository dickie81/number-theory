/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 430–432 of 1732

File 108 of 430: the parts `rows22310R_430` … `rows22310R_432` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22844 tests: row 100 columns 0–34, row 100 columns 35–43, row 100 columns
44–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_430 : rowsJ2 100 101 0 35 ≤ 244101866881993 := by decide +kernel

theorem rows22310R_431 : rowsJ2 100 101 35 44 ≤ 97803910235891 := by decide +kernel

theorem rows22310R_432 : rowsJ2 100 101 44 51 ≤ 215112601878296 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_430
#print axioms SieveCert.rows22310R_432
