/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 418–420 of 1732

File 105 of 430: the parts `rows22310R_418` … `rows22310R_420` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22985 tests: row 99 columns 0–34, row 99 columns 35–43, row 99 columns
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

theorem rows22310R_418 : rowsJ2 99 100 0 35 ≤ 262298302711031 := by decide +kernel

theorem rows22310R_419 : rowsJ2 99 100 35 44 ≤ 90650743964167 := by decide +kernel

theorem rows22310R_420 : rowsJ2 99 100 44 51 ≤ 212173445979406 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_418
#print axioms SieveCert.rows22310R_420
