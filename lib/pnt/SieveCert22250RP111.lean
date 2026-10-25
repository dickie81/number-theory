/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1058–1068 of 5796

File 111 of 465: the parts `rows22250R_1058` … `rows22250R_1068` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99637 tests: row 64 columns 26–26, row 64 columns 27–27, row 64 columns
28–28, row 64 columns 29–29, row 64 columns 30–30, row 64 columns 31–31, row 64 columns 32–32, row 64 columns 33–33,
row 64 columns 34–34, row 64 columns 35–35, row 64 columns 36–36), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1058 : rowsJ2 64 65 26 27 ≤ 3249370653 := by decide +kernel

theorem rows22250R_1059 : rowsJ2 64 65 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1060 : rowsJ2 64 65 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1061 : rowsJ2 64 65 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1062 : rowsJ2 64 65 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1063 : rowsJ2 64 65 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1064 : rowsJ2 64 65 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1065 : rowsJ2 64 65 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1066 : rowsJ2 64 65 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1067 : rowsJ2 64 65 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1068 : rowsJ2 64 65 36 37 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1058
#print axioms SieveCert.rows22250R_1068
