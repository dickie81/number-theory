/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5113–5125 of 5796

File 420 of 465: the parts `rows22250R_5113` … `rows22250R_5125` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96375 tests: row 167 columns 0–42, row 167 columns 43–45, row 167 columns
46–47, row 167 columns 48–48, row 167 columns 49–49, row 167 columns 50–50, row 167 columns 51–51, row 167 columns
52–52, row 167 columns 53–53, row 167 columns 54–54, row 167 columns 55–55, row 167 columns 56–56, row 167 columns
57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5113 : rowsJ2 167 168 0 43 ≤ 6735210748047 := by decide +kernel

theorem rows22250R_5114 : rowsJ2 167 168 43 46 ≤ 10872156940669 := by decide +kernel

theorem rows22250R_5115 : rowsJ2 167 168 46 48 ≤ 11072443404610 := by decide +kernel

theorem rows22250R_5116 : rowsJ2 167 168 48 49 ≤ 6839775855354 := by decide +kernel

theorem rows22250R_5117 : rowsJ2 167 168 49 50 ≤ 7773146150306 := by decide +kernel

theorem rows22250R_5118 : rowsJ2 167 168 50 51 ≤ 8752381857363 := by decide +kernel

theorem rows22250R_5119 : rowsJ2 167 168 51 52 ≤ 9775768930658 := by decide +kernel

theorem rows22250R_5120 : rowsJ2 167 168 52 53 ≤ 10841745125932 := by decide +kernel

theorem rows22250R_5121 : rowsJ2 167 168 53 54 ≤ 11948892355166 := by decide +kernel

theorem rows22250R_5122 : rowsJ2 167 168 54 55 ≤ 13095929780895 := by decide +kernel

theorem rows22250R_5123 : rowsJ2 167 168 55 56 ≤ 14281707605691 := by decide +kernel

theorem rows22250R_5124 : rowsJ2 167 168 56 57 ≤ 15505201518277 := by decide +kernel

theorem rows22250R_5125 : rowsJ2 167 168 57 58 ≤ 15360020020431 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5113
#print axioms SieveCert.rows22250R_5125
