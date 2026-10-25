/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1669–1676 of 5796

File 166 of 465: the parts `rows22250R_1669` … `rows22250R_1676` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 86528 tests: row 76 columns 49–49, row 76 columns 50–50, row 76 columns
51–51, row 76 columns 52–52, row 76 columns 53–53, row 76 columns 54–54, row 76 columns 55–55, row 76 columns
56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1669 : rowsJ2 76 77 49 50 ≤ 819304215852 := by decide +kernel

theorem rows22250R_1670 : rowsJ2 76 77 50 51 ≤ 1232257760112 := by decide +kernel

theorem rows22250R_1671 : rowsJ2 76 77 51 52 ≤ 1773830988613 := by decide +kernel

theorem rows22250R_1672 : rowsJ2 76 77 52 53 ≤ 2462053342485 := by decide +kernel

theorem rows22250R_1673 : rowsJ2 76 77 53 54 ≤ 2970994383063 := by decide +kernel

theorem rows22250R_1674 : rowsJ2 76 77 54 55 ≤ 3341152054849 := by decide +kernel

theorem rows22250R_1675 : rowsJ2 76 77 55 56 ≤ 3680874342172 := by decide +kernel

theorem rows22250R_1676 : rowsJ2 76 77 56 57 ≤ 4081819231414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1669
#print axioms SieveCert.rows22250R_1676
