/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1147–1150 of 1732

File 288 of 430: the parts `rows22310R_1147` … `rows22310R_1150` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26418 tests: row 144 columns 60–66, row 144 columns 67–70, row 144 columns
71–73, row 144 columns 74–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1147 : rowsJ2 144 145 60 67 ≤ 9381312300604 := by decide +kernel

theorem rows22310R_1148 : rowsJ2 144 145 67 71 ≤ 10349196251035 := by decide +kernel

theorem rows22310R_1149 : rowsJ2 144 145 71 74 ≤ 8867084611295 := by decide +kernel

theorem rows22310R_1150 : rowsJ2 144 145 74 77 ≤ 8825230850548 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1147
#print axioms SieveCert.rows22310R_1150
