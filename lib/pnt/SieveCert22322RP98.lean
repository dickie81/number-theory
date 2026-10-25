/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 376–379 of 561

File 98 of 143: the parts `rows22322R_376` … `rows22322R_379` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29967 tests: row 109 columns 63–69, row 109 columns 70–299, row 110 columns
0–50, row 110 columns 51–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_376 : rowsJ2 109 110 63 70 ≤ 1404125966850 := by decide +kernel

theorem rows22322R_377 : rowsJ2 109 110 70 300 ≤ 334313945002844 := by decide +kernel

theorem rows22322R_378 : rowsJ2 110 111 0 51 ≤ 309813371954870 := by decide +kernel

theorem rows22322R_379 : rowsJ2 110 111 51 57 ≤ 41336970348588 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_376
#print axioms SieveCert.rows22322R_379
