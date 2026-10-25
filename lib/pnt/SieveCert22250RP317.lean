/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4164–4177 of 4715

File 317 of 351: the parts `rows22250R_4164` … `rows22250R_4177` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96144 tests: row 158 columns 52–52, row 158 columns 53–53, row 158 columns
54–54, row 158 columns 55–55, row 158 columns 56–56, row 158 columns 57–57, row 158 columns 58–58, row 158 columns
59–59, row 158 columns 60–60, row 158 columns 61–62, row 158 columns 63–65, row 158 columns 66–339, row 159 columns
0–40, row 159 columns 41–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4164 : rowsJ2 158 159 52 53 ≤ 16222031453963 := by decide +kernel

theorem rows22250R_4165 : rowsJ2 158 159 53 54 ≤ 17683150973606 := by decide +kernel

theorem rows22250R_4166 : rowsJ2 158 159 54 55 ≤ 15900905316837 := by decide +kernel

theorem rows22250R_4167 : rowsJ2 158 159 55 56 ≤ 14227625248155 := by decide +kernel

theorem rows22250R_4168 : rowsJ2 158 159 56 57 ≤ 12660029274014 := by decide +kernel

theorem rows22250R_4169 : rowsJ2 158 159 57 58 ≤ 11195073264471 := by decide +kernel

theorem rows22250R_4170 : rowsJ2 158 159 58 59 ≤ 9829938218253 := by decide +kernel

theorem rows22250R_4171 : rowsJ2 158 159 59 60 ≤ 8562019174855 := by decide +kernel

theorem rows22250R_4172 : rowsJ2 158 159 60 61 ≤ 7388915186830 := by decide +kernel

theorem rows22250R_4173 : rowsJ2 158 159 61 63 ≤ 11626935580888 := by decide +kernel

theorem rows22250R_4174 : rowsJ2 158 159 63 66 ≤ 10895454942243 := by decide +kernel

theorem rows22250R_4175 : rowsJ2 158 159 66 340 ≤ 2641942690759654 := by decide +kernel

theorem rows22250R_4176 : rowsJ2 159 160 0 41 ≤ 10587213573640 := by decide +kernel

theorem rows22250R_4177 : rowsJ2 159 160 41 44 ≤ 15208242546585 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4164
#print axioms SieveCert.rows22250R_4177
