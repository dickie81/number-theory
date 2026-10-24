/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 167–170 of 561

File 44 of 142: the parts `rows22325R_167` … `rows22325R_170` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29512 tests: row 79 columns 0–34, row 79 columns 35–60, row 79 columns 61–67,
row 79 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_167 : rowsJ2 79 80 0 35 ≤ 517220435303350 := by decide +kernel

theorem rows22325R_168 : rowsJ2 79 80 35 61 ≤ 660948272709213 := by decide +kernel

theorem rows22325R_169 : rowsJ2 79 80 61 68 ≤ 9128598822929 := by decide +kernel

theorem rows22325R_170 : rowsJ2 79 80 68 72 ≤ 12598900151644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_167
#print axioms SieveCert.rows22325R_170
