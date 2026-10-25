/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1035–1041 of 4715

File 95 of 351: the parts `rows22250R_1035` … `rows22250R_1041` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 92276 tests: row 63 columns 54–54, row 63 columns 55–55, row 63 columns
56–56, row 63 columns 57–57, row 63 columns 58–58, row 63 columns 59–59, row 63 columns 60–60), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1035 : rowsJ2 63 64 54 55 ≤ 8755055547884 := by decide +kernel

theorem rows22250R_1036 : rowsJ2 63 64 55 56 ≤ 9772660975787 := by decide +kernel

theorem rows22250R_1037 : rowsJ2 63 64 56 57 ≤ 10604585362549 := by decide +kernel

theorem rows22250R_1038 : rowsJ2 63 64 57 58 ≤ 11270432895292 := by decide +kernel

theorem rows22250R_1039 : rowsJ2 63 64 58 59 ≤ 12030910807443 := by decide +kernel

theorem rows22250R_1040 : rowsJ2 63 64 59 60 ≤ 11515464992452 := by decide +kernel

theorem rows22250R_1041 : rowsJ2 63 64 60 61 ≤ 10988685736518 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1035
#print axioms SieveCert.rows22250R_1041
