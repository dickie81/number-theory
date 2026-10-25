/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4823–4833 of 5796

File 398 of 465: the parts `rows22250R_4823` … `rows22250R_4833` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 90300 tests: row 156 columns 51–52, row 156 columns 53–53, row 156 columns
54–54, row 156 columns 55–55, row 156 columns 56–56, row 156 columns 57–57, row 156 columns 58–58, row 156 columns
59–59, row 156 columns 60–60, row 156 columns 61–61, row 156 columns 62–62), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4823 : rowsJ2 156 157 51 53 ≤ 8513436851147 := by decide +kernel

theorem rows22250R_4824 : rowsJ2 156 157 53 54 ≤ 5311866045774 := by decide +kernel

theorem rows22250R_4825 : rowsJ2 156 157 54 55 ≤ 6070984462177 := by decide +kernel

theorem rows22250R_4826 : rowsJ2 156 157 55 56 ≤ 6869814620932 := by decide +kernel

theorem rows22250R_4827 : rowsJ2 156 157 56 57 ≤ 7706865382918 := by decide +kernel

theorem rows22250R_4828 : rowsJ2 156 157 57 58 ≤ 8580764118847 := by decide +kernel

theorem rows22250R_4829 : rowsJ2 156 157 58 59 ≤ 9490250737777 := by decide +kernel

theorem rows22250R_4830 : rowsJ2 156 157 59 60 ≤ 10434172235347 := by decide +kernel

theorem rows22250R_4831 : rowsJ2 156 157 60 61 ≤ 11411477730049 := by decide +kernel

theorem rows22250R_4832 : rowsJ2 156 157 61 62 ≤ 12421213958959 := by decide +kernel

theorem rows22250R_4833 : rowsJ2 156 157 62 63 ≤ 13462521207764 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4823
#print axioms SieveCert.rows22250R_4833
