/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1099–1110 of 5796

File 115 of 465: the parts `rows22250R_1099` … `rows22250R_1110` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99320 tests: row 65 columns 22–23, row 65 columns 24–24, row 65 columns
25–25, row 65 columns 26–26, row 65 columns 27–27, row 65 columns 28–28, row 65 columns 29–29, row 65 columns 30–30,
row 65 columns 31–31, row 65 columns 32–32, row 65 columns 33–33, row 65 columns 34–34), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1099 : rowsJ2 65 66 22 24 ≤ 32772379814 := by decide +kernel

theorem rows22250R_1100 : rowsJ2 65 66 24 25 ≤ 6551591135 := by decide +kernel

theorem rows22250R_1101 : rowsJ2 65 66 25 26 ≤ 3264128820 := by decide +kernel

theorem rows22250R_1102 : rowsJ2 65 66 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1103 : rowsJ2 65 66 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1104 : rowsJ2 65 66 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1105 : rowsJ2 65 66 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1106 : rowsJ2 65 66 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1107 : rowsJ2 65 66 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1108 : rowsJ2 65 66 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1109 : rowsJ2 65 66 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1110 : rowsJ2 65 66 34 35 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1099
#print axioms SieveCert.rows22250R_1110
