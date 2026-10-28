/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 372–377 of 4715

File 35 of 351: the parts `rows22250R_372` … `rows22250R_377` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, work 85248 in units of a depth-4 test: row 44 columns 30–30, row 44 columns
31–31, row 44 columns 32–32, row 44 columns 33–33, row 44 columns 34–34, row 44 columns 35–35), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_372 : rowsJ2 44 45 30 31 ≤ 273538766424 := by decide +kernel

theorem rows22250R_373 : rowsJ2 44 45 31 32 ≤ 255554194412 := by decide +kernel

theorem rows22250R_374 : rowsJ2 44 45 32 33 ≤ 233667075585 := by decide +kernel

theorem rows22250R_375 : rowsJ2 44 45 33 34 ≤ 202185761628 := by decide +kernel

theorem rows22250R_376 : rowsJ2 44 45 34 35 ≤ 173996959966 := by decide +kernel

theorem rows22250R_377 : rowsJ2 44 45 35 36 ≤ 142768179135 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_372
#print axioms SieveCert.rows22250R_377
