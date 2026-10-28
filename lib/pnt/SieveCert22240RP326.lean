/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4130–4142 of 5066

File 326 of 387: the parts `rows22240R_4130` … `rows22240R_4142` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99910 in units of a depth-4 test: row 144 columns 0–25, row 144 columns
26–47, row 144 columns 48–50, row 144 columns 51–52, row 144 columns 53–53, row 144 columns 54–54, row 144 columns
55–55, row 144 columns 56–56, row 144 columns 57–57, row 144 columns 58–58, row 144 columns 59–59, row 144 columns
60–60, row 144 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4130 : rowsJ2 144 145 0 26 ≤ 2911962720036 := by decide +kernel

theorem rows22240R_4131 : rowsJ2 144 145 26 48 ≤ 5762423242691 := by decide +kernel

theorem rows22240R_4132 : rowsJ2 144 145 48 51 ≤ 9493653191797 := by decide +kernel

theorem rows22240R_4133 : rowsJ2 144 145 51 53 ≤ 9882339852455 := by decide +kernel

theorem rows22240R_4134 : rowsJ2 144 145 53 54 ≤ 6162565071093 := by decide +kernel

theorem rows22240R_4135 : rowsJ2 144 145 54 55 ≤ 7040883348609 := by decide +kernel

theorem rows22240R_4136 : rowsJ2 144 145 55 56 ≤ 7964837306869 := by decide +kernel

theorem rows22240R_4137 : rowsJ2 144 145 56 57 ≤ 8932688370553 := by decide +kernel

theorem rows22240R_4138 : rowsJ2 144 145 57 58 ≤ 9942795649921 := by decide +kernel

theorem rows22240R_4139 : rowsJ2 144 145 58 59 ≤ 10993642188842 := by decide +kernel

theorem rows22240R_4140 : rowsJ2 144 145 59 60 ≤ 12083794212173 := by decide +kernel

theorem rows22240R_4141 : rowsJ2 144 145 60 61 ≤ 13211940164531 := by decide +kernel

theorem rows22240R_4142 : rowsJ2 144 145 61 62 ≤ 14357380977018 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4130
#print axioms SieveCert.rows22240R_4142
