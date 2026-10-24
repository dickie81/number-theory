/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 531–535 of 561

File 135 of 142: the parts `rows22325R_531` … `rows22325R_535` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 28544 tests: rows 163–163, rows 164–164, rows 165–166, rows 167–168, rows
169–170), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_531 : rows2 163 164 ≤ 4187879796402256 := by decide +kernel

theorem rows22325R_532 : rows2 164 165 ≤ 4334066461551613 := by decide +kernel

theorem rows22325R_533 : rows2 165 167 ≤ 9108059233561565 := by decide +kernel

theorem rows22325R_534 : rows2 167 169 ≤ 9696164977123397 := by decide +kernel

theorem rows22325R_535 : rows2 169 171 ≤ 10285340473192939 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_531
#print axioms SieveCert.rows22325R_535
