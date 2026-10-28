/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1525–1534 of 5066

File 143 of 387: the parts `rows22240R_1525` … `rows22240R_1534` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 97920 in units of a depth-4 test: row 73 columns 46–46, row 73 columns
47–47, row 73 columns 48–48, row 73 columns 49–49, row 73 columns 50–50, row 73 columns 51–51, row 73 columns 52–52,
row 73 columns 53–53, row 73 columns 54–54, row 73 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22240R_1525 : rowsJ2 73 74 46 47 ≤ 355648881867 := by decide +kernel

theorem rows22240R_1526 : rowsJ2 73 74 47 48 ≤ 759339944735 := by decide +kernel

theorem rows22240R_1527 : rowsJ2 73 74 48 49 ≤ 1450718777985 := by decide +kernel

theorem rows22240R_1528 : rowsJ2 73 74 49 50 ≤ 2237198749733 := by decide +kernel

theorem rows22240R_1529 : rowsJ2 73 74 50 51 ≤ 2855005703811 := by decide +kernel

theorem rows22240R_1530 : rowsJ2 73 74 51 52 ≤ 3426761068935 := by decide +kernel

theorem rows22240R_1531 : rowsJ2 73 74 52 53 ≤ 4025609739310 := by decide +kernel

theorem rows22240R_1532 : rowsJ2 73 74 53 54 ≤ 4449346610936 := by decide +kernel

theorem rows22240R_1533 : rowsJ2 73 74 54 55 ≤ 4644415881388 := by decide +kernel

theorem rows22240R_1534 : rowsJ2 73 74 55 56 ≤ 4542257913105 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1525
#print axioms SieveCert.rows22240R_1534
