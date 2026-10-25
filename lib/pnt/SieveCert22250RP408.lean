/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4952–4966 of 5796

File 408 of 465: the parts `rows22250R_4952` … `rows22250R_4966` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 91852 tests: row 160 columns 68–68, row 160 columns 69–69, row 160 columns
70–70, row 160 columns 71–72, row 160 columns 73–75, row 160 columns 76–359, row 161 columns 0–43, row 161 columns
44–47, row 161 columns 48–49, row 161 columns 50–50, row 161 columns 51–51, row 161 columns 52–52, row 161 columns
53–53, row 161 columns 54–54, row 161 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4952 : rowsJ2 160 161 68 69 ≤ 5602173731883 := by decide +kernel

theorem rows22250R_4953 : rowsJ2 160 161 69 70 ≤ 4813869281242 := by decide +kernel

theorem rows22250R_4954 : rowsJ2 160 161 70 71 ≤ 4088727374699 := by decide +kernel

theorem rows22250R_4955 : rowsJ2 160 161 71 73 ≤ 6249168956372 := by decide +kernel

theorem rows22250R_4956 : rowsJ2 160 161 73 76 ≤ 5454978719467 := by decide +kernel

theorem rows22250R_4957 : rowsJ2 160 161 76 360 ≤ 2019658780745654 := by decide +kernel

theorem rows22250R_4958 : rowsJ2 161 162 0 44 ≤ 2746202508076 := by decide +kernel

theorem rows22250R_4959 : rowsJ2 161 162 44 48 ≤ 9559678909232 := by decide +kernel

theorem rows22250R_4960 : rowsJ2 161 162 48 50 ≤ 8513232870902 := by decide +kernel

theorem rows22250R_4961 : rowsJ2 161 162 50 51 ≤ 5365690753490 := by decide +kernel

theorem rows22250R_4962 : rowsJ2 161 162 51 52 ≤ 6166265249510 := by decide +kernel

theorem rows22250R_4963 : rowsJ2 161 162 52 53 ≤ 7010401955647 := by decide +kernel

theorem rows22250R_4964 : rowsJ2 161 162 53 54 ≤ 7896411820032 := by decide +kernel

theorem rows22250R_4965 : rowsJ2 161 162 54 55 ≤ 8822743329545 := by decide +kernel

theorem rows22250R_4966 : rowsJ2 161 162 55 56 ≤ 9787975366401 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4952
#print axioms SieveCert.rows22250R_4966
