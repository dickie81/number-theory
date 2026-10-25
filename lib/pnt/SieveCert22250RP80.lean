/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 745–751 of 5796

File 80 of 465: the parts `rows22250R_745` … `rows22250R_751` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 87963 tests: row 56 columns 29–29, row 56 columns 30–30, row 56 columns
31–31, row 56 columns 32–32, row 56 columns 33–33, row 56 columns 34–34, row 56 columns 35–35), each a sum of
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

theorem rows22250R_745 : rowsJ2 56 57 29 30 ≤ 41425017848 := by decide +kernel

theorem rows22250R_746 : rowsJ2 56 57 30 31 ≤ 32769948869 := by decide +kernel

theorem rows22250R_747 : rowsJ2 56 57 31 32 ≤ 22453356593 := by decide +kernel

theorem rows22250R_748 : rowsJ2 56 57 32 33 ≤ 15681682770 := by decide +kernel

theorem rows22250R_749 : rowsJ2 56 57 33 34 ≤ 8509650594 := by decide +kernel

theorem rows22250R_750 : rowsJ2 56 57 34 35 ≤ 4901321744 := by decide +kernel

theorem rows22250R_751 : rowsJ2 56 57 35 36 ≤ 868346477 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_745
#print axioms SieveCert.rows22250R_751
