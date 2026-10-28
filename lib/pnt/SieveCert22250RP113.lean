/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1254–1261 of 4715

File 113 of 351: the parts `rows22250R_1254` … `rows22250R_1261` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 94506 in units of a depth-4 test: row 68 columns 52–52, row 68 columns
53–53, row 68 columns 54–54, row 68 columns 55–55, row 68 columns 56–56, row 68 columns 57–57, row 68 columns 58–58,
row 68 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1254 : rowsJ2 68 69 52 53 ≤ 5725229646683 := by decide +kernel

theorem rows22250R_1255 : rowsJ2 68 69 53 54 ≤ 6328646795343 := by decide +kernel

theorem rows22250R_1256 : rowsJ2 68 69 54 55 ≤ 6899746109796 := by decide +kernel

theorem rows22250R_1257 : rowsJ2 68 69 55 56 ≤ 7489588140326 := by decide +kernel

theorem rows22250R_1258 : rowsJ2 68 69 56 57 ≤ 7464034095374 := by decide +kernel

theorem rows22250R_1259 : rowsJ2 68 69 57 58 ≤ 7058694921187 := by decide +kernel

theorem rows22250R_1260 : rowsJ2 68 69 58 59 ≤ 6658094656796 := by decide +kernel

theorem rows22250R_1261 : rowsJ2 68 69 59 60 ≤ 6314200619787 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1254
#print axioms SieveCert.rows22250R_1261
