/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 14–19 of 561

File 4 of 143: the parts `rows22322R_14` … `rows22322R_19` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–299, row 37 columns 0–34,
row 37 columns 35–299, row 38 columns 0–34, row 38 columns 35–299), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_14 : rowsJ2 36 37 0 35 ≤ 2771514011710031 := by decide +kernel

theorem rows22322R_15 : rowsJ2 36 37 35 300 ≤ 168528842666003 := by decide +kernel

theorem rows22322R_16 : rowsJ2 37 38 0 35 ≤ 2690739482466329 := by decide +kernel

theorem rows22322R_17 : rowsJ2 37 38 35 300 ≤ 229859377453266 := by decide +kernel

theorem rows22322R_18 : rowsJ2 38 39 0 35 ≤ 2609664781889120 := by decide +kernel

theorem rows22322R_19 : rowsJ2 38 39 35 300 ≤ 279714877146069 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_14
#print axioms SieveCert.rows22322R_19
