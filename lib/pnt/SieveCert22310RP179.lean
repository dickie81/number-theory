/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 711–715 of 1732

File 179 of 430: the parts `rows22310R_711` … `rows22310R_715` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29440 tests: row 117 columns 86–87, row 117 columns 88–89, row 117 columns
90–91, row 117 columns 92–93, row 117 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_711 : rowsJ2 117 118 86 88 ≤ 275613479893 := by decide +kernel

theorem rows22310R_712 : rowsJ2 117 118 88 90 ≤ 781821182021 := by decide +kernel

theorem rows22310R_713 : rowsJ2 117 118 90 92 ≤ 1391752492293 := by decide +kernel

theorem rows22310R_714 : rowsJ2 117 118 92 94 ≤ 1268737173310 := by decide +kernel

theorem rows22310R_715 : rowsJ2 117 118 94 96 ≤ 1024983442610 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_711
#print axioms SieveCert.rows22310R_715
