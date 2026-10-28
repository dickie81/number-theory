/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 743–754 of 4715

File 71 of 351: the parts `rows22250R_743` … `rows22250R_754` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 89882 in units of a depth-4 test: row 56 columns 42–42, row 56 columns
43–43, row 56 columns 44–44, row 56 columns 45–45, row 56 columns 46–46, row 56 columns 47–47, row 56 columns 48–48,
row 56 columns 49–49, row 56 columns 50–50, row 56 columns 51–51, row 56 columns 52–52, row 56 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_743 : rowsJ2 56 57 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_744 : rowsJ2 56 57 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_745 : rowsJ2 56 57 44 45 ≤ 71613548570 := by decide +kernel

theorem rows22250R_746 : rowsJ2 56 57 45 46 ≤ 281083346225 := by decide +kernel

theorem rows22250R_747 : rowsJ2 56 57 46 47 ≤ 838569629038 := by decide +kernel

theorem rows22250R_748 : rowsJ2 56 57 47 48 ≤ 1665269207502 := by decide +kernel

theorem rows22250R_749 : rowsJ2 56 57 48 49 ≤ 2460684573673 := by decide +kernel

theorem rows22250R_750 : rowsJ2 56 57 49 50 ≤ 3365716079779 := by decide +kernel

theorem rows22250R_751 : rowsJ2 56 57 50 51 ≤ 4521397617169 := by decide +kernel

theorem rows22250R_752 : rowsJ2 56 57 51 52 ≤ 5924048163194 := by decide +kernel

theorem rows22250R_753 : rowsJ2 56 57 52 53 ≤ 7270562212517 := by decide +kernel

theorem rows22250R_754 : rowsJ2 56 57 53 54 ≤ 8705994864046 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_743
#print axioms SieveCert.rows22250R_754
