/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5033–5046 of 5796

File 414 of 465: the parts `rows22250R_5033` … `rows22250R_5046` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 90822 tests: row 163 columns 68–68, row 163 columns 69–70, row 163 columns
71–73, row 163 columns 74–359, row 164 columns 0–43, row 164 columns 44–46, row 164 columns 47–48, row 164 columns
49–49, row 164 columns 50–50, row 164 columns 51–51, row 164 columns 52–52, row 164 columns 53–53, row 164 columns
54–54, row 164 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_5033 : rowsJ2 163 164 68 69 ≤ 4656408372882 := by decide +kernel

theorem rows22250R_5034 : rowsJ2 163 164 69 71 ≤ 7191549703723 := by decide +kernel

theorem rows22250R_5035 : rowsJ2 163 164 71 74 ≤ 6439151296336 := by decide +kernel

theorem rows22250R_5036 : rowsJ2 163 164 74 360 ≤ 2334101557678328 := by decide +kernel

theorem rows22250R_5037 : rowsJ2 164 165 0 44 ≤ 5552945053314 := by decide +kernel

theorem rows22250R_5038 : rowsJ2 164 165 44 47 ≤ 9361402195538 := by decide +kernel

theorem rows22250R_5039 : rowsJ2 164 165 47 49 ≤ 9741452646050 := by decide +kernel

theorem rows22250R_5040 : rowsJ2 164 165 49 50 ≤ 6073297978013 := by decide +kernel

theorem rows22250R_5041 : rowsJ2 164 165 50 51 ≤ 6937719706098 := by decide +kernel

theorem rows22250R_5042 : rowsJ2 164 165 51 52 ≤ 7846811693715 := by decide +kernel

theorem rows22250R_5043 : rowsJ2 164 165 52 53 ≤ 8798870549979 := by decide +kernel

theorem rows22250R_5044 : rowsJ2 164 165 53 54 ≤ 9792337247442 := by decide +kernel

theorem rows22250R_5045 : rowsJ2 164 165 54 55 ≤ 10825789725015 := by decide +kernel

theorem rows22250R_5046 : rowsJ2 164 165 55 56 ≤ 11897936176492 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5033
#print axioms SieveCert.rows22250R_5046
