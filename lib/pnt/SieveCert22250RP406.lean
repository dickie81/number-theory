/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4925–4940 of 5796

File 406 of 465: the parts `rows22250R_4925` … `rows22250R_4940` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95274 tests: row 159 columns 69–69, row 159 columns 70–70, row 159 columns
71–72, row 159 columns 73–74, row 159 columns 75–78, row 159 columns 79–359, row 160 columns 0–44, row 160 columns
45–47, row 160 columns 48–49, row 160 columns 50–50, row 160 columns 51–51, row 160 columns 52–52, row 160 columns
53–53, row 160 columns 54–54, row 160 columns 55–55, row 160 columns 56–56), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4925 : rowsJ2 159 160 69 70 ≤ 5110213173883 := by decide +kernel

theorem rows22250R_4926 : rowsJ2 159 160 70 71 ≤ 4365746684913 := by decide +kernel

theorem rows22250R_4927 : rowsJ2 159 160 71 73 ≤ 6743295097644 := by decide +kernel

theorem rows22250R_4928 : rowsJ2 159 160 73 75 ≤ 4491137591537 := by decide +kernel

theorem rows22250R_4929 : rowsJ2 159 160 75 79 ≤ 4081925632023 := by decide +kernel

theorem rows22250R_4930 : rowsJ2 159 160 79 360 ≤ 1908438425758320 := by decide +kernel

theorem rows22250R_4931 : rowsJ2 160 161 0 45 ≤ 3488863131377 := by decide +kernel

theorem rows22250R_4932 : rowsJ2 160 161 45 48 ≤ 7028566195408 := by decide +kernel

theorem rows22250R_4933 : rowsJ2 160 161 48 50 ≤ 7704872752155 := by decide +kernel

theorem rows22250R_4934 : rowsJ2 160 161 50 51 ≤ 4908121936265 := by decide +kernel

theorem rows22250R_4935 : rowsJ2 160 161 51 52 ≤ 5673499513167 := by decide +kernel

theorem rows22250R_4936 : rowsJ2 160 161 52 53 ≤ 6482683420149 := by decide +kernel

theorem rows22250R_4937 : rowsJ2 160 161 53 54 ≤ 7333943156364 := by decide +kernel

theorem rows22250R_4938 : rowsJ2 160 161 54 55 ≤ 8225686110289 := by decide +kernel

theorem rows22250R_4939 : rowsJ2 160 161 55 56 ≤ 9156450283695 := by decide +kernel

theorem rows22250R_4940 : rowsJ2 160 161 56 57 ≤ 10124897652780 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4925
#print axioms SieveCert.rows22250R_4940
