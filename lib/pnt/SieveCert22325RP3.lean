/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 9–13 of 561

File 3 of 142: the parts `rows22325R_9` … `rows22325R_13` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_9 : rows2 32 33 ≤ 2803028215883863 := by decide +kernel

theorem rows22325R_10 : rows2 33 34 ≤ 2849447049571631 := by decide +kernel

theorem rows22325R_11 : rows2 34 35 ≤ 2874576687072559 := by decide +kernel

theorem rows22325R_12 : rowsJ2 35 36 0 35 ≤ 2792787485518892 := by decide +kernel

theorem rows22325R_13 : rowsJ2 35 36 35 300 ≤ 87400767263607 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_9
#print axioms SieveCert.rows22325R_13
