/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1578–1586 of 5066

File 147 of 387: the parts `rows22240R_1578` … `rows22240R_1586` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 97603 in units of a depth-4 test: row 74 columns 49–49, row 74 columns
50–50, row 74 columns 51–51, row 74 columns 52–52, row 74 columns 53–53, row 74 columns 54–54, row 74 columns 55–55,
row 74 columns 56–56, row 74 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1578 : rowsJ2 74 75 49 50 ≤ 2168763687383 := by decide +kernel

theorem rows22240R_1579 : rowsJ2 74 75 50 51 ≤ 2729943887686 := by decide +kernel

theorem rows22240R_1580 : rowsJ2 74 75 51 52 ≤ 3193259924492 := by decide +kernel

theorem rows22240R_1581 : rowsJ2 74 75 52 53 ≤ 3731401245132 := by decide +kernel

theorem rows22240R_1582 : rowsJ2 74 75 53 54 ≤ 4042749536243 := by decide +kernel

theorem rows22240R_1583 : rowsJ2 74 75 54 55 ≤ 4175461869635 := by decide +kernel

theorem rows22240R_1584 : rowsJ2 74 75 55 56 ≤ 3837679151437 := by decide +kernel

theorem rows22240R_1585 : rowsJ2 74 75 56 57 ≤ 3555302040774 := by decide +kernel

theorem rows22240R_1586 : rowsJ2 74 75 57 58 ≤ 3213371745416 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1578
#print axioms SieveCert.rows22240R_1586
