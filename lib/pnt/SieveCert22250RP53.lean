/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 506–512 of 5796

File 53 of 465: the parts `rows22250R_506` … `rows22250R_512` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 93477 tests: row 48 columns 42–42, row 48 columns 43–43, row 48 columns
44–44, row 48 columns 45–45, row 48 columns 46–46, row 48 columns 47–47, row 48 columns 48–359), each a sum of
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

theorem rows22250R_506 : rowsJ2 48 49 42 43 ≤ 17077474936 := by decide +kernel

theorem rows22250R_507 : rowsJ2 48 49 43 44 ≤ 10050089668 := by decide +kernel

theorem rows22250R_508 : rowsJ2 48 49 44 45 ≤ 8101298326 := by decide +kernel

theorem rows22250R_509 : rowsJ2 48 49 45 46 ≤ 5649078099 := by decide +kernel

theorem rows22250R_510 : rowsJ2 48 49 46 47 ≤ 5150682869 := by decide +kernel

theorem rows22250R_511 : rowsJ2 48 49 47 48 ≤ 130409181228 := by decide +kernel

theorem rows22250R_512 : rowsJ2 48 49 48 360 ≤ 569578225372 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_506
#print axioms SieveCert.rows22250R_512
