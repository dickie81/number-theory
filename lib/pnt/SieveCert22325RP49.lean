/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 187–189 of 561

File 49 of 142: the parts `rows22325R_187` … `rows22325R_189` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23062 tests: row 82 columns 0–36, row 82 columns 37–61, row 82 columns
62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_187 : rowsJ2 82 83 0 37 ≤ 596623331604416 := by decide +kernel

theorem rows22325R_188 : rowsJ2 82 83 37 62 ≤ 439401817571565 := by decide +kernel

theorem rows22325R_189 : rowsJ2 82 83 62 68 ≤ 2967691761669 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_187
#print axioms SieveCert.rows22325R_189
