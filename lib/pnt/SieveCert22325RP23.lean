/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 91–94 of 561

File 23 of 142: the parts `rows22325R_91` … `rows22325R_94` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23814 tests: row 61 columns 0–34, row 61 columns 35–44, row 61 columns 45–60,
row 61 columns 61–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_91 : rowsJ2 61 62 0 35 ≤ 890737826388277 := by decide +kernel

theorem rows22325R_92 : rowsJ2 61 62 35 45 ≤ 560789695467537 := by decide +kernel

theorem rows22325R_93 : rowsJ2 61 62 45 61 ≤ 797790723642426 := by decide +kernel

theorem rows22325R_94 : rowsJ2 61 62 61 300 ≤ 32362079578020 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_91
#print axioms SieveCert.rows22325R_94
