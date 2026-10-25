/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 914–917 of 1732

File 229 of 430: the parts `rows22310R_914` … `rows22310R_917` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26680 tests: row 128 columns 86–87, row 128 columns 88–89, row 128 columns
90–92, row 128 columns 93–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_914 : rowsJ2 128 129 86 88 ≤ 21325007751 := by decide +kernel

theorem rows22310R_915 : rowsJ2 128 129 88 90 ≤ 0 := by decide +kernel

theorem rows22310R_916 : rowsJ2 128 129 90 93 ≤ 0 := by decide +kernel

theorem rows22310R_917 : rowsJ2 128 129 93 96 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_914
#print axioms SieveCert.rows22310R_917
