/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1233–1242 of 5066

File 119 of 387: the parts `rows22240R_1233` … `rows22240R_1242` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 94508 in units of a depth-4 test: row 67 columns 46–46, row 67 columns
47–47, row 67 columns 48–48, row 67 columns 49–49, row 67 columns 50–50, row 67 columns 51–51, row 67 columns 52–52,
row 67 columns 53–53, row 67 columns 54–54, row 67 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1233 : rowsJ2 67 68 46 47 ≤ 374426550720 := by decide +kernel

theorem rows22240R_1234 : rowsJ2 67 68 47 48 ≤ 799431829607 := by decide +kernel

theorem rows22240R_1235 : rowsJ2 67 68 48 49 ≤ 1527314314197 := by decide +kernel

theorem rows22240R_1236 : rowsJ2 67 68 49 50 ≤ 2355319119057 := by decide +kernel

theorem rows22240R_1237 : rowsJ2 67 68 50 51 ≤ 3213815174949 := by decide +kernel

theorem rows22240R_1238 : rowsJ2 67 68 51 52 ≤ 4228575748951 := by decide +kernel

theorem rows22240R_1239 : rowsJ2 67 68 52 53 ≤ 5335326381556 := by decide +kernel

theorem rows22240R_1240 : rowsJ2 67 68 53 54 ≤ 6269235156597 := by decide +kernel

theorem rows22240R_1241 : rowsJ2 67 68 54 55 ≤ 6979855335905 := by decide +kernel

theorem rows22240R_1242 : rowsJ2 67 68 55 56 ≤ 7645838308156 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1233
#print axioms SieveCert.rows22240R_1242
