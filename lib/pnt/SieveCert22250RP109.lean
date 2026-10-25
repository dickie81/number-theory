/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1041–1048 of 5796

File 109 of 465: the parts `rows22250R_1041` … `rows22250R_1048` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 96404 tests: row 63 columns 52–52, row 63 columns 53–53, row 63 columns
54–54, row 63 columns 55–55, row 63 columns 56–56, row 63 columns 57–57, row 63 columns 58–58, row 63 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1041 : rowsJ2 63 64 52 53 ≤ 2835265082324 := by decide +kernel

theorem rows22250R_1042 : rowsJ2 63 64 53 54 ≤ 3714420425218 := by decide +kernel

theorem rows22250R_1043 : rowsJ2 63 64 54 55 ≤ 4613345220416 := by decide +kernel

theorem rows22250R_1044 : rowsJ2 63 64 55 56 ≤ 5696655846527 := by decide +kernel

theorem rows22250R_1045 : rowsJ2 63 64 56 57 ≤ 6981630827629 := by decide +kernel

theorem rows22250R_1046 : rowsJ2 63 64 57 58 ≤ 8180448462730 := by decide +kernel

theorem rows22250R_1047 : rowsJ2 63 64 58 59 ≤ 9197353586769 := by decide +kernel

theorem rows22250R_1048 : rowsJ2 63 64 59 60 ≤ 10185404679857 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1041
#print axioms SieveCert.rows22250R_1048
