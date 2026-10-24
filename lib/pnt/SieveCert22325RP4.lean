/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 14–19 of 561

File 4 of 142: the parts `rows22325R_14` … `rows22325R_19` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–299, row 37 columns 0–34,
row 37 columns 35–299, row 38 columns 0–34, row 38 columns 35–299), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_14 : rowsJ2 36 37 0 35 ≤ 2710999764591408 := by decide +kernel

theorem rows22325R_15 : rowsJ2 36 37 35 300 ≤ 158029547730023 := by decide +kernel

theorem rows22325R_16 : rowsJ2 37 38 0 35 ≤ 2628814408789613 := by decide +kernel

theorem rows22325R_17 : rowsJ2 37 38 35 300 ≤ 214935698286985 := by decide +kernel

theorem rows22325R_18 : rowsJ2 38 39 0 35 ≤ 2546970362222274 := by decide +kernel

theorem rows22325R_19 : rowsJ2 38 39 35 300 ≤ 260707153644574 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_14
#print axioms SieveCert.rows22325R_19
