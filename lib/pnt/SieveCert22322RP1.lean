/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 0–3 of 561

File 1 of 143: the parts `rows22322R_0` … `rows22322R_3` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_0 : rows2 0 19 ≤ 7200333070982656 := by decide +kernel

theorem rows22322R_1 : rows2 19 23 ≤ 5632422717782420 := by decide +kernel

theorem rows22322R_2 : rows2 23 25 ≤ 3621383706761259 := by decide +kernel

theorem rows22322R_3 : rows2 25 27 ≤ 4190102603424334 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_0
#print axioms SieveCert.rows22322R_3
