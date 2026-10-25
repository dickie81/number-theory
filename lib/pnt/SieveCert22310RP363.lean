/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1444–1447 of 1732

File 363 of 430: the parts `rows22310R_1444` … `rows22310R_1447` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28035 tests: row 172 columns 59–62, row 172 columns 63–66, row 172 columns
67–70, row 172 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1444 : rowsJ2 172 173 59 63 ≤ 32036544091620 := by decide +kernel

theorem rows22310R_1445 : rowsJ2 172 173 63 67 ≤ 33978721247496 := by decide +kernel

theorem rows22310R_1446 : rowsJ2 172 173 67 71 ≤ 22399899769909 := by decide +kernel

theorem rows22310R_1447 : rowsJ2 172 173 71 76 ≤ 15628348133780 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1444
#print axioms SieveCert.rows22310R_1447
