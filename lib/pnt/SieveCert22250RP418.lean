/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5085–5099 of 5796

File 418 of 465: the parts `rows22250R_5085` … `rows22250R_5099` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97925 tests: row 165 columns 69–70, row 165 columns 71–74, row 165 columns
75–359, row 166 columns 0–42, row 166 columns 43–45, row 166 columns 46–47, row 166 columns 48–48, row 166 columns
49–49, row 166 columns 50–50, row 166 columns 51–51, row 166 columns 52–52, row 166 columns 53–53, row 166 columns
54–54, row 166 columns 55–55, row 166 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5085 : rowsJ2 165 166 69 71 ≤ 6125828656731 := by decide +kernel

theorem rows22250R_5086 : rowsJ2 165 166 71 75 ≤ 6088960719972 := by decide +kernel

theorem rows22250R_5087 : rowsJ2 165 166 75 360 ≤ 2533536719817134 := by decide +kernel

theorem rows22250R_5088 : rowsJ2 166 167 0 43 ≤ 5576025112696 := by decide +kernel

theorem rows22250R_5089 : rowsJ2 166 167 43 46 ≤ 9699508521259 := by decide +kernel

theorem rows22250R_5090 : rowsJ2 166 167 46 48 ≤ 10089570003872 := by decide +kernel

theorem rows22250R_5091 : rowsJ2 166 167 48 49 ≤ 6289043171299 := by decide +kernel

theorem rows22250R_5092 : rowsJ2 166 167 49 50 ≤ 7183227119992 := by decide +kernel

theorem rows22250R_5093 : rowsJ2 166 167 50 51 ≤ 8123473583892 := by decide +kernel

theorem rows22250R_5094 : rowsJ2 166 167 51 52 ≤ 9108020014042 := by decide +kernel

theorem rows22250R_5095 : rowsJ2 166 167 52 53 ≤ 10135255801075 := by decide +kernel

theorem rows22250R_5096 : rowsJ2 166 167 53 54 ≤ 11203714460719 := by decide +kernel

theorem rows22250R_5097 : rowsJ2 166 167 54 55 ≤ 12312066555961 := by decide +kernel

theorem rows22250R_5098 : rowsJ2 166 167 55 56 ≤ 13459113310350 := by decide +kernel

theorem rows22250R_5099 : rowsJ2 166 167 56 57 ≤ 14643780872532 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5085
#print axioms SieveCert.rows22250R_5099
