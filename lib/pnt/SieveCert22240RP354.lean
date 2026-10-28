/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4526–4540 of 5066

File 354 of 387: the parts `rows22240R_4526` … `rows22240R_4540` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99789 in units of a depth-4 test: row 160 columns 51–51, row 160
columns 52–52, row 160 columns 53–53, row 160 columns 54–54, row 160 columns 55–55, row 160 columns 56–56, row 160
columns 57–57, row 160 columns 58–58, row 160 columns 59–59, row 160 columns 60–60, row 160 columns 61–62, row 160
columns 63–64, row 160 columns 65–132, row 160 columns 133–339, row 161 columns 0–40), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4526 : rowsJ2 160 161 51 52 ≤ 15958750621771 := by decide +kernel

theorem rows22240R_4527 : rowsJ2 160 161 52 53 ≤ 17435856077956 := by decide +kernel

theorem rows22240R_4528 : rowsJ2 160 161 53 54 ≤ 18960923973637 := by decide +kernel

theorem rows22240R_4529 : rowsJ2 160 161 54 55 ≤ 17089618682330 := by decide +kernel

theorem rows22240R_4530 : rowsJ2 160 161 55 56 ≤ 15331125679498 := by decide +kernel

theorem rows22240R_4531 : rowsJ2 160 161 56 57 ≤ 13681962446099 := by decide +kernel

theorem rows22240R_4532 : rowsJ2 160 161 57 58 ≤ 12138886791549 := by decide +kernel

theorem rows22240R_4533 : rowsJ2 160 161 58 59 ≤ 10698896052788 := by decide +kernel

theorem rows22240R_4534 : rowsJ2 160 161 59 60 ≤ 9359217981902 := by decide +kernel

theorem rows22240R_4535 : rowsJ2 160 161 60 61 ≤ 8117289362831 := by decide +kernel

theorem rows22240R_4536 : rowsJ2 160 161 61 63 ≤ 12888152767290 := by decide +kernel

theorem rows22240R_4537 : rowsJ2 160 161 63 65 ≤ 9037830799900 := by decide +kernel

theorem rows22240R_4538 : rowsJ2 160 161 65 133 ≤ 1343931577521151 := by decide +kernel

theorem rows22240R_4539 : rowsJ2 160 161 133 340 ≤ 1253132254268104 := by decide +kernel

theorem rows22240R_4540 : rowsJ2 161 162 0 41 ≤ 12204245960396 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4526
#print axioms SieveCert.rows22240R_4540
