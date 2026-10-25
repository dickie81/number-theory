/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 286–290 of 5796

File 22 of 465: the parts `rows22250R_286` … `rows22250R_290` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 95477 tests: row 39 columns 33–33, row 39 columns 34–34, row 39 columns
35–35, row 39 columns 36–36, row 39 columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_286 : rowsJ2 39 40 33 34 ≤ 509741624615 := by decide +kernel

theorem rows22250R_287 : rowsJ2 39 40 34 35 ≤ 560729160639 := by decide +kernel

theorem rows22250R_288 : rowsJ2 39 40 35 36 ≤ 584858776833 := by decide +kernel

theorem rows22250R_289 : rowsJ2 39 40 36 37 ≤ 581583164385 := by decide +kernel

theorem rows22250R_290 : rowsJ2 39 40 37 38 ≤ 564961357258 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_286
#print axioms SieveCert.rows22250R_290
