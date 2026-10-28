/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2584–2598 of 5066

File 222 of 387: the parts `rows22240R_2584` … `rows22240R_2598` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 93318 in units of a depth-4 test: row 96 columns 43–43, row 96 columns
44–44, row 96 columns 45–45, row 96 columns 46–46, row 96 columns 47–47, row 96 columns 48–48, row 96 columns 49–49,
row 96 columns 50–50, row 96 columns 51–51, row 96 columns 52–53, row 96 columns 54–55, row 96 columns 56–57, row 96
columns 58–60, row 96 columns 61–65, row 96 columns 66–70), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2584 : rowsJ2 96 97 43 44 ≤ 16602412107652 := by decide +kernel

theorem rows22240R_2585 : rowsJ2 96 97 44 45 ≤ 14834102267978 := by decide +kernel

theorem rows22240R_2586 : rowsJ2 96 97 45 46 ≤ 13086674719238 := by decide +kernel

theorem rows22240R_2587 : rowsJ2 96 97 46 47 ≤ 11418333744495 := by decide +kernel

theorem rows22240R_2588 : rowsJ2 96 97 47 48 ≤ 9768180777206 := by decide +kernel

theorem rows22240R_2589 : rowsJ2 96 97 48 49 ≤ 8293413894911 := by decide +kernel

theorem rows22240R_2590 : rowsJ2 96 97 49 50 ≤ 6928775896184 := by decide +kernel

theorem rows22240R_2591 : rowsJ2 96 97 50 51 ≤ 5730931362302 := by decide +kernel

theorem rows22240R_2592 : rowsJ2 96 97 51 52 ≤ 4696895605963 := by decide +kernel

theorem rows22240R_2593 : rowsJ2 96 97 52 54 ≤ 6585681112917 := by decide +kernel

theorem rows22240R_2594 : rowsJ2 96 97 54 56 ≤ 2543801866099 := by decide +kernel

theorem rows22240R_2595 : rowsJ2 96 97 56 58 ≤ 328036500521 := by decide +kernel

theorem rows22240R_2596 : rowsJ2 96 97 58 61 ≤ 0 := by decide +kernel

theorem rows22240R_2597 : rowsJ2 96 97 61 66 ≤ 0 := by decide +kernel

theorem rows22240R_2598 : rowsJ2 96 97 66 71 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2584
#print axioms SieveCert.rows22240R_2598
