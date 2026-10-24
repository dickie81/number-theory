/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 24–27 of 561

File 6 of 142: the parts `rows22325R_24` … `rows22325R_27` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–299, row 42 columns 0–34,
row 42 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_24 : rowsJ2 41 42 0 35 ≤ 2301626532705024 := by decide +kernel

theorem rows22325R_25 : rowsJ2 41 42 35 300 ≤ 360267645548537 := by decide +kernel

theorem rows22325R_26 : rowsJ2 42 43 0 35 ≤ 2220574338432283 := by decide +kernel

theorem rows22325R_27 : rowsJ2 42 43 35 300 ≤ 390288365562535 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_24
#print axioms SieveCert.rows22325R_27
