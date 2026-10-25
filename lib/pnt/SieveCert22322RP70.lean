/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 268–270 of 561

File 70 of 143: the parts `rows22322R_268` … `rows22322R_270` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22953 tests: row 92 columns 75–80, row 92 columns 81–299, row 93 columns
0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_268 : rowsJ2 92 93 75 81 ≤ 9297098791446 := by decide +kernel

theorem rows22322R_269 : rowsJ2 92 93 81 300 ≤ 750279158063266 := by decide +kernel

theorem rows22322R_270 : rowsJ2 93 94 0 53 ≤ 647960804194478 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_268
#print axioms SieveCert.rows22322R_270
