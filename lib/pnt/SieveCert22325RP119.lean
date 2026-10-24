/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 460–462 of 561

File 119 of 142: the parts `rows22325R_460` … `rows22325R_462` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22886 tests: row 128 columns 45–52, row 128 columns 53–299, row 129 columns
0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_460 : rowsJ2 128 129 45 53 ≤ 109302037977370 := by decide +kernel

theorem rows22325R_461 : rowsJ2 128 129 53 300 ≤ 1944657328480965 := by decide +kernel

theorem rows22325R_462 : rowsJ2 129 130 0 45 ≤ 136756474618247 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_460
#print axioms SieveCert.rows22325R_462
