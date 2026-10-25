/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 167–170 of 561

File 44 of 143: the parts `rows22322R_167` … `rows22322R_170` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29512 tests: row 79 columns 0–34, row 79 columns 35–60, row 79 columns 61–67,
row 79 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_167 : rowsJ2 79 80 0 35 ≤ 538185972938443 := by decide +kernel

theorem rows22322R_168 : rowsJ2 79 80 35 61 ≤ 663503897138342 := by decide +kernel

theorem rows22322R_169 : rowsJ2 79 80 61 68 ≤ 9162074817370 := by decide +kernel

theorem rows22322R_170 : rowsJ2 79 80 68 72 ≤ 12627199440283 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_167
#print axioms SieveCert.rows22322R_170
