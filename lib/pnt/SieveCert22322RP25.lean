/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 98–100 of 561

File 25 of 143: the parts `rows22322R_98` … `rows22322R_100` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22979 tests: row 63 columns 0–34, row 63 columns 35–44, row 63 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_98 : rowsJ2 63 64 0 35 ≤ 849026168493088 := by decide +kernel

theorem rows22322R_99 : rowsJ2 63 64 35 45 ≤ 582386259956050 := by decide +kernel

theorem rows22322R_100 : rowsJ2 63 64 45 300 ≤ 815385450423234 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_98
#print axioms SieveCert.rows22322R_100
