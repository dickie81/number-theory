/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 388–391 of 561

File 101 of 142: the parts `rows22325R_388` … `rows22325R_391` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29703 tests: row 112 columns 0–49, row 112 columns 50–55, row 112 columns
56–61, row 112 columns 62–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_388 : rowsJ2 112 113 0 50 ≤ 277574404045384 := by decide +kernel

theorem rows22325R_389 : rowsJ2 112 113 50 56 ≤ 48673688236087 := by decide +kernel

theorem rows22325R_390 : rowsJ2 112 113 56 62 ≤ 31867678443842 := by decide +kernel

theorem rows22325R_391 : rowsJ2 112 113 62 70 ≤ 7558754831730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_388
#print axioms SieveCert.rows22325R_391
