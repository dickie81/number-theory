/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 9–13 of 561

File 3 of 143: the parts `rows22322R_9` … `rows22322R_13` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_9 : rows2 32 33 ≤ 2845583695474137 := by decide +kernel

theorem rows22322R_10 : rows2 33 34 ≤ 2900113264730511 := by decide +kernel

theorem rows22322R_11 : rows2 34 35 ≤ 2932634336022982 := by decide +kernel

theorem rows22322R_12 : rowsJ2 35 36 0 35 ≤ 2852257523393192 := by decide +kernel

theorem rows22322R_13 : rowsJ2 35 36 35 300 ≤ 92823520754353 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_9
#print axioms SieveCert.rows22322R_13
