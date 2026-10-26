/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 91–94 of 561

File 23 of 143: the parts `rows22322R_91` … `rows22322R_94` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23814 tests: row 61 columns 0–34, row 61 columns 35–44, row 61 columns 45–60,
row 61 columns 61–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_91 : rowsJ2 61 62 0 35 ≤ 947823638874935 := by decide +kernel

theorem rows22322R_92 : rowsJ2 61 62 35 45 ≤ 563747002395122 := by decide +kernel

theorem rows22322R_93 : rowsJ2 61 62 45 61 ≤ 800703282825474 := by decide +kernel

theorem rows22322R_94 : rowsJ2 61 62 61 300 ≤ 32485535220707 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_91
#print axioms SieveCert.rows22322R_94
