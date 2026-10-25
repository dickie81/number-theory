/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1167–1177 of 5796

File 121 of 465: the parts `rows22250R_1167` … `rows22250R_1177` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 96349 tests: row 66 columns 46–46, row 66 columns 47–47, row 66 columns
48–48, row 66 columns 49–49, row 66 columns 50–50, row 66 columns 51–51, row 66 columns 52–52, row 66 columns 53–53,
row 66 columns 54–54, row 66 columns 55–55, row 66 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_1167 : rowsJ2 66 67 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1168 : rowsJ2 66 67 47 48 ≤ 106647641145 := by decide +kernel

theorem rows22250R_1169 : rowsJ2 66 67 48 49 ≤ 477977551931 := by decide +kernel

theorem rows22250R_1170 : rowsJ2 66 67 49 50 ≤ 890056643091 := by decide +kernel

theorem rows22250R_1171 : rowsJ2 66 67 50 51 ≤ 1338671502197 := by decide +kernel

theorem rows22250R_1172 : rowsJ2 66 67 51 52 ≤ 1927013219989 := by decide +kernel

theorem rows22250R_1173 : rowsJ2 66 67 52 53 ≤ 2761811821897 := by decide +kernel

theorem rows22250R_1174 : rowsJ2 66 67 53 54 ≤ 3618190872459 := by decide +kernel

theorem rows22250R_1175 : rowsJ2 66 67 54 55 ≤ 4493827207792 := by decide +kernel

theorem rows22250R_1176 : rowsJ2 66 67 55 56 ≤ 5510662645931 := by decide +kernel

theorem rows22250R_1177 : rowsJ2 66 67 56 57 ≤ 6608655483266 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1167
#print axioms SieveCert.rows22250R_1177
