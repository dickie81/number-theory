/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 9–13 of 549

File 3 of 140: the parts `rows22335R_9` … `rows22335R_13` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_9 : rows2 32 33 ≤ 2799408267098850 := by decide +kernel

theorem rows22335R_10 : rows2 33 34 ≤ 2845774199513135 := by decide +kernel

theorem rows22335R_11 : rows2 34 35 ≤ 2870876800783585 := by decide +kernel

theorem rows22335R_12 : rowsJ2 35 36 0 35 ≤ 2789193970846348 := by decide +kernel

theorem rows22335R_13 : rowsJ2 35 36 35 300 ≤ 87291132675914 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_9
#print axioms SieveCert.rows22335R_13
