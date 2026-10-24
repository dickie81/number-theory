/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 148–150 of 561

File 39 of 142: the parts `rows22325R_148` … `rows22325R_150` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23371 tests: row 75 columns 72–299, row 76 columns 0–34, row 76 columns
35–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_148 : rowsJ2 75 76 72 300 ≤ 26638534379919 := by decide +kernel

theorem rows22325R_149 : rowsJ2 76 77 0 35 ≤ 524720979558704 := by decide +kernel

theorem rows22325R_150 : rowsJ2 76 77 35 61 ≤ 803810368272260 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_148
#print axioms SieveCert.rows22325R_150
