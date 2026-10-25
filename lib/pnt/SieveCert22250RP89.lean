/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 832–843 of 5796

File 89 of 465: the parts `rows22250R_832` … `rows22250R_843` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 98444 tests: row 58 columns 43–43, row 58 columns 44–44, row 58 columns
45–45, row 58 columns 46–46, row 58 columns 47–47, row 58 columns 48–48, row 58 columns 49–49, row 58 columns 50–50,
row 58 columns 51–51, row 58 columns 52–52, row 58 columns 53–53, row 58 columns 54–54), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_832 : rowsJ2 58 59 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_833 : rowsJ2 58 59 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_834 : rowsJ2 58 59 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_835 : rowsJ2 58 59 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_836 : rowsJ2 58 59 47 48 ≤ 114562215131 := by decide +kernel

theorem rows22250R_837 : rowsJ2 58 59 48 49 ≤ 513449397884 := by decide +kernel

theorem rows22250R_838 : rowsJ2 58 59 49 50 ≤ 956109854181 := by decide +kernel

theorem rows22250R_839 : rowsJ2 58 59 50 51 ≤ 1438017484276 := by decide +kernel

theorem rows22250R_840 : rowsJ2 58 59 51 52 ≤ 2070021434103 := by decide +kernel

theorem rows22250R_841 : rowsJ2 58 59 52 53 ≤ 2966772417013 := by decide +kernel

theorem rows22250R_842 : rowsJ2 58 59 53 54 ≤ 3886705384775 := by decide +kernel

theorem rows22250R_843 : rowsJ2 58 59 54 55 ≤ 4827324766015 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_832
#print axioms SieveCert.rows22250R_843
