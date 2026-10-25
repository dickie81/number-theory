/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3875–3888 of 4715

File 297 of 351: the parts `rows22250R_3875` … `rows22250R_3888` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 92112 tests: row 145 columns 69–70, row 145 columns 71–73, row 145 columns
74–79, row 145 columns 80–339, row 146 columns 0–43, row 146 columns 44–47, row 146 columns 48–49, row 146 columns
50–51, row 146 columns 52–52, row 146 columns 53–53, row 146 columns 54–54, row 146 columns 55–55, row 146 columns
56–56, row 146 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3875 : rowsJ2 145 146 69 71 ≤ 7121308654993 := by decide +kernel

theorem rows22250R_3876 : rowsJ2 145 146 71 74 ≤ 6212618714951 := by decide +kernel

theorem rows22250R_3877 : rowsJ2 145 146 74 80 ≤ 2896818636055 := by decide +kernel

theorem rows22250R_3878 : rowsJ2 145 146 80 340 ≤ 1468843765871180 := by decide +kernel

theorem rows22250R_3879 : rowsJ2 146 147 0 44 ≤ 2106184231578 := by decide +kernel

theorem rows22250R_3880 : rowsJ2 146 147 44 48 ≤ 8336423195724 := by decide +kernel

theorem rows22250R_3881 : rowsJ2 146 147 48 50 ≤ 7968538951909 := by decide +kernel

theorem rows22250R_3882 : rowsJ2 146 147 50 52 ≤ 11117004468535 := by decide +kernel

theorem rows22250R_3883 : rowsJ2 146 147 52 53 ≤ 6869007574033 := by decide +kernel

theorem rows22250R_3884 : rowsJ2 146 147 53 54 ≤ 7807608373904 := by decide +kernel

theorem rows22250R_3885 : rowsJ2 146 147 54 55 ≤ 8792512410252 := by decide +kernel

theorem rows22250R_3886 : rowsJ2 146 147 55 56 ≤ 9821994956239 := by decide +kernel

theorem rows22250R_3887 : rowsJ2 146 147 56 57 ≤ 10894480707665 := by decide +kernel

theorem rows22250R_3888 : rowsJ2 146 147 57 58 ≤ 12008536284574 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3875
#print axioms SieveCert.rows22250R_3888
