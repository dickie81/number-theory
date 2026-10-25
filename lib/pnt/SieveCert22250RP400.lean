/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4847–4860 of 5796

File 400 of 465: the parts `rows22250R_4847` … `rows22250R_4860` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 91798 tests: row 156 columns 83–359, row 157 columns 0–44, row 157 columns
45–48, row 157 columns 49–50, row 157 columns 51–51, row 157 columns 52–52, row 157 columns 53–53, row 157 columns
54–54, row 157 columns 55–55, row 157 columns 56–56, row 157 columns 57–57, row 157 columns 58–58, row 157 columns
59–59, row 157 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4847 : rowsJ2 156 157 83 360 ≤ 1579794095392676 := by decide +kernel

theorem rows22250R_4848 : rowsJ2 157 158 0 45 ≤ 1483557976397 := by decide +kernel

theorem rows22250R_4849 : rowsJ2 157 158 45 49 ≤ 6979711819949 := by decide +kernel

theorem rows22250R_4850 : rowsJ2 157 158 49 51 ≤ 6682510168994 := by decide +kernel

theorem rows22250R_4851 : rowsJ2 157 158 51 52 ≤ 4312544627165 := by decide +kernel

theorem rows22250R_4852 : rowsJ2 157 158 52 53 ≤ 5020265708332 := by decide +kernel

theorem rows22250R_4853 : rowsJ2 157 158 53 54 ≤ 5770783649055 := by decide +kernel

theorem rows22250R_4854 : rowsJ2 157 158 54 55 ≤ 6562387961757 := by decide +kernel

theorem rows22250R_4855 : rowsJ2 157 158 55 56 ≤ 7393499837677 := by decide +kernel

theorem rows22250R_4856 : rowsJ2 157 158 56 57 ≤ 8262665139143 := by decide +kernel

theorem rows22250R_4857 : rowsJ2 157 158 57 58 ≤ 9168547986625 := by decide +kernel

theorem rows22250R_4858 : rowsJ2 157 158 58 59 ≤ 10109924901549 := by decide +kernel

theorem rows22250R_4859 : rowsJ2 157 158 59 60 ≤ 11085679469720 := by decide +kernel

theorem rows22250R_4860 : rowsJ2 157 158 60 61 ≤ 12094797494316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4847
#print axioms SieveCert.rows22250R_4860
