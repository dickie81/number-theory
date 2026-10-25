/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 906–909 of 1732

File 227 of 430: the parts `rows22310R_906` … `rows22310R_909` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29979 tests: row 127 columns 111–399, row 128 columns 0–34, row 128 columns
35–67, row 128 columns 68–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_906 : rowsJ2 127 128 111 400 ≤ 944029965966447 := by decide +kernel

theorem rows22310R_907 : rowsJ2 128 129 0 35 ≤ 140777488892922 := by decide +kernel

theorem rows22310R_908 : rowsJ2 128 129 35 68 ≤ 295428525213849 := by decide +kernel

theorem rows22310R_909 : rowsJ2 128 129 68 74 ≤ 251123343069 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_906
#print axioms SieveCert.rows22310R_909
