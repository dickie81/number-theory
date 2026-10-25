/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4898–4913 of 5796

File 404 of 465: the parts `rows22250R_4898` … `rows22250R_4913` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99021 tests: row 158 columns 70–70, row 158 columns 71–71, row 158 columns
72–73, row 158 columns 74–76, row 158 columns 77–140, row 158 columns 141–359, row 159 columns 0–44, row 159 columns
45–48, row 159 columns 49–50, row 159 columns 51–51, row 159 columns 52–52, row 159 columns 53–53, row 159 columns
54–54, row 159 columns 55–55, row 159 columns 56–56, row 159 columns 57–57), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4898 : rowsJ2 158 159 70 71 ≤ 4663584443023 := by decide +kernel

theorem rows22250R_4899 : rowsJ2 158 159 71 72 ≤ 3961225826412 := by decide +kernel

theorem rows22250R_4900 : rowsJ2 158 159 72 74 ≤ 6054558992470 := by decide +kernel

theorem rows22250R_4901 : rowsJ2 158 159 74 77 ≤ 5285352321425 := by decide +kernel

theorem rows22250R_4902 : rowsJ2 158 159 77 141 ≤ 663613882590442 := by decide +kernel

theorem rows22250R_4903 : rowsJ2 158 159 141 360 ≤ 1143116339171214 := by decide +kernel

theorem rows22250R_4904 : rowsJ2 159 160 0 45 ≤ 2652235699879 := by decide +kernel

theorem rows22250R_4905 : rowsJ2 159 160 45 49 ≤ 9238592233693 := by decide +kernel

theorem rows22250R_4906 : rowsJ2 159 160 49 51 ≤ 8230714286270 := by decide +kernel

theorem rows22250R_4907 : rowsJ2 159 160 51 52 ≤ 5188665545943 := by decide +kernel

theorem rows22250R_4908 : rowsJ2 159 160 52 53 ≤ 5963599189844 := by decide +kernel

theorem rows22250R_4909 : rowsJ2 159 160 53 54 ≤ 6780828523232 := by decide +kernel

theorem rows22250R_4910 : rowsJ2 159 160 54 55 ≤ 7638720855345 := by decide +kernel

theorem rows22250R_4911 : rowsJ2 159 160 55 56 ≤ 8535774396393 := by decide +kernel

theorem rows22250R_4912 : rowsJ2 159 160 56 57 ≤ 9470611491076 := by decide +kernel

theorem rows22250R_4913 : rowsJ2 159 160 57 58 ≤ 10441972447280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4898
#print axioms SieveCert.rows22250R_4913
