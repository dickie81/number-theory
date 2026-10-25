/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 112–115 of 1732

File 28 of 430: the parts `rows22310R_112` … `rows22310R_115` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 63 columns 0–34, row 63 columns 35–43, row 63 columns 44–49,
row 63 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_112 : rowsJ2 63 64 0 35 ≤ 1109370943742023 := by decide +kernel

theorem rows22310R_113 : rowsJ2 63 64 35 44 ≤ 358439926875255 := by decide +kernel

theorem rows22310R_114 : rowsJ2 63 64 44 50 ≤ 156314306090753 := by decide +kernel

theorem rows22310R_115 : rowsJ2 63 64 50 55 ≤ 120837516901958 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_112
#print axioms SieveCert.rows22310R_115
