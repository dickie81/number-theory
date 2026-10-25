/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5059–5072 of 5796

File 416 of 465: the parts `rows22250R_5059` … `rows22250R_5072` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 91028 tests: row 164 columns 68–69, row 164 columns 70–71, row 164 columns
72–75, row 164 columns 76–359, row 165 columns 0–43, row 165 columns 44–46, row 165 columns 47–48, row 165 columns
49–49, row 165 columns 50–50, row 165 columns 51–51, row 165 columns 52–52, row 165 columns 53–53, row 165 columns
54–54, row 165 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_5059 : rowsJ2 164 165 68 70 ≤ 8018425821309 := by decide +kernel

theorem rows22250R_5060 : rowsJ2 164 165 70 72 ≤ 5446953209799 := by decide +kernel

theorem rows22250R_5061 : rowsJ2 164 165 72 76 ≤ 5207373420661 := by decide +kernel

theorem rows22250R_5062 : rowsJ2 164 165 76 360 ≤ 2436105217463022 := by decide +kernel

theorem rows22250R_5063 : rowsJ2 165 166 0 44 ≤ 6716448941224 := by decide +kernel

theorem rows22250R_5064 : rowsJ2 165 166 44 47 ≤ 10490912885626 := by decide +kernel

theorem rows22250R_5065 : rowsJ2 165 166 47 49 ≤ 10688062368480 := by decide +kernel

theorem rows22250R_5066 : rowsJ2 165 166 49 50 ≤ 6603663867270 := by decide +kernel

theorem rows22250R_5067 : rowsJ2 165 166 50 51 ≤ 7505783188123 := by decide +kernel

theorem rows22250R_5068 : rowsJ2 165 166 51 52 ≤ 8452373281778 := by decide +kernel

theorem rows22250R_5069 : rowsJ2 165 166 52 53 ≤ 9441776603636 := by decide +kernel

theorem rows22250R_5070 : rowsJ2 165 166 53 54 ≤ 10472479803076 := by decide +kernel

theorem rows22250R_5071 : rowsJ2 165 166 54 55 ≤ 11543106482306 := by decide +kernel

theorem rows22250R_5072 : rowsJ2 165 166 55 56 ≤ 12652410643162 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5059
#print axioms SieveCert.rows22250R_5072
