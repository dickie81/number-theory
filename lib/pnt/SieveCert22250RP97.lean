/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 917–924 of 5796

File 97 of 465: the parts `rows22250R_917` … `rows22250R_924` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 88222 tests: row 60 columns 51–51, row 60 columns 52–52, row 60 columns
53–53, row 60 columns 54–54, row 60 columns 55–55, row 60 columns 56–56, row 60 columns 57–57, row 60 columns
58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_917 : rowsJ2 60 61 51 52 ≤ 2032315694089 := by decide +kernel

theorem rows22250R_918 : rowsJ2 60 61 52 53 ≤ 2912732228058 := by decide +kernel

theorem rows22250R_919 : rowsJ2 60 61 53 54 ≤ 3815908483670 := by decide +kernel

theorem rows22250R_920 : rowsJ2 60 61 54 55 ≤ 4739394346744 := by decide +kernel

theorem rows22250R_921 : rowsJ2 60 61 55 56 ≤ 5852303962611 := by decide +kernel

theorem rows22250R_922 : rowsJ2 60 61 56 57 ≤ 7211386752329 := by decide +kernel

theorem rows22250R_923 : rowsJ2 60 61 57 58 ≤ 8599007251767 := by decide +kernel

theorem rows22250R_924 : rowsJ2 60 61 58 59 ≤ 9842670444108 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_917
#print axioms SieveCert.rows22250R_924
