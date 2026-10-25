/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3973–3986 of 4715

File 304 of 351: the parts `rows22250R_3973` … `rows22250R_3986` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94379 tests: row 149 columns 70–73, row 149 columns 74–339, row 150 columns
0–43, row 150 columns 44–46, row 150 columns 47–48, row 150 columns 49–49, row 150 columns 50–50, row 150 columns
51–51, row 150 columns 52–52, row 150 columns 53–53, row 150 columns 54–54, row 150 columns 55–55, row 150 columns
56–56, row 150 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3973 : rowsJ2 149 150 70 74 ≤ 5930634980036 := by decide +kernel

theorem rows22250R_3974 : rowsJ2 149 150 74 340 ≤ 1880492195006276 := by decide +kernel

theorem rows22250R_3975 : rowsJ2 150 151 0 44 ≤ 5200296477294 := by decide +kernel

theorem rows22250R_3976 : rowsJ2 150 151 44 47 ≤ 9532330310493 := by decide +kernel

theorem rows22250R_3977 : rowsJ2 150 151 47 49 ≤ 10169537042519 := by decide +kernel

theorem rows22250R_3978 : rowsJ2 150 151 49 50 ≤ 6404582892370 := by decide +kernel

theorem rows22250R_3979 : rowsJ2 150 151 50 51 ≤ 7356435574502 := by decide +kernel

theorem rows22250R_3980 : rowsJ2 150 151 51 52 ≤ 8359471419393 := by decide +kernel

theorem rows22250R_3981 : rowsJ2 150 151 52 53 ≤ 9411674984064 := by decide +kernel

theorem rows22250R_3982 : rowsJ2 150 151 53 54 ≤ 10511205382894 := by decide +kernel

theorem rows22250R_3983 : rowsJ2 150 151 54 55 ≤ 11656387069493 := by decide +kernel

theorem rows22250R_3984 : rowsJ2 150 151 55 56 ≤ 12845701492524 := by decide +kernel

theorem rows22250R_3985 : rowsJ2 150 151 56 57 ≤ 14077779570314 := by decide +kernel

theorem rows22250R_3986 : rowsJ2 150 151 57 58 ≤ 15351394934843 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3973
#print axioms SieveCert.rows22250R_3986
