/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1191–1194 of 1732

File 299 of 430: the parts `rows22310R_1191` … `rows22310R_1194` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27692 tests: row 147 columns 80–82, row 147 columns 83–85, row 147 columns
86–89, row 147 columns 90–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1191 : rowsJ2 147 148 80 83 ≤ 5442911181515 := by decide +kernel

theorem rows22310R_1192 : rowsJ2 147 148 83 86 ≤ 2888402072429 := by decide +kernel

theorem rows22310R_1193 : rowsJ2 147 148 86 90 ≤ 972697563221 := by decide +kernel

theorem rows22310R_1194 : rowsJ2 147 148 90 94 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1191
#print axioms SieveCert.rows22310R_1194
