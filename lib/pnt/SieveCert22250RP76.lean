/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 705–714 of 5796

File 76 of 465: the parts `rows22250R_705` … `rows22250R_714` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 95820 tests: row 55 columns 23–24, row 55 columns 25–25, row 55 columns
26–26, row 55 columns 27–27, row 55 columns 28–28, row 55 columns 29–29, row 55 columns 30–30, row 55 columns 31–31,
row 55 columns 32–32, row 55 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_705 : rowsJ2 55 56 23 25 ≤ 290231023809 := by decide +kernel

theorem rows22250R_706 : rowsJ2 55 56 25 26 ≤ 113803256154 := by decide +kernel

theorem rows22250R_707 : rowsJ2 55 56 26 27 ≤ 94764717196 := by decide +kernel

theorem rows22250R_708 : rowsJ2 55 56 27 28 ≤ 78843705441 := by decide +kernel

theorem rows22250R_709 : rowsJ2 55 56 28 29 ≤ 66070392945 := by decide +kernel

theorem rows22250R_710 : rowsJ2 55 56 29 30 ≤ 55990682505 := by decide +kernel

theorem rows22250R_711 : rowsJ2 55 56 30 31 ≤ 43491618416 := by decide +kernel

theorem rows22250R_712 : rowsJ2 55 56 31 32 ≤ 33563081895 := by decide +kernel

theorem rows22250R_713 : rowsJ2 55 56 32 33 ≤ 23281173428 := by decide +kernel

theorem rows22250R_714 : rowsJ2 55 56 33 34 ≤ 16085999271 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_705
#print axioms SieveCert.rows22250R_714
