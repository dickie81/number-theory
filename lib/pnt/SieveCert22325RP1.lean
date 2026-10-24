/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 0–3 of 561

File 1 of 142: the parts `rows22325R_0` … `rows22325R_3` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_0 : rows2 0 19 ≤ 7163789198408252 := by decide +kernel

theorem rows22325R_1 : rows2 19 23 ≤ 5605374083743901 := by decide +kernel

theorem rows22325R_2 : rows2 23 25 ≤ 3604353760422242 := by decide +kernel

theorem rows22325R_3 : rows2 25 27 ≤ 4167805493034617 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_0
#print axioms SieveCert.rows22325R_3
