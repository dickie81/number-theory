/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3916–3929 of 4715

File 300 of 351: the parts `rows22250R_3916` … `rows22250R_3929` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 97366 in units of a depth-4 test: row 147 columns 60–60, row 147
columns 61–61, row 147 columns 62–62, row 147 columns 63–63, row 147 columns 64–64, row 147 columns 65–65, row 147
columns 66–66, row 147 columns 67–68, row 147 columns 69–70, row 147 columns 71–74, row 147 columns 75–339, row 148
columns 0–43, row 148 columns 44–47, row 148 columns 48–49), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3916 : rowsJ2 147 148 60 61 ≤ 12442424164389 := by decide +kernel

theorem rows22250R_3917 : rowsJ2 147 148 61 62 ≤ 11109445820420 := by decide +kernel

theorem rows22250R_3918 : rowsJ2 147 148 62 63 ≤ 9860910918784 := by decide +kernel

theorem rows22250R_3919 : rowsJ2 147 148 63 64 ≤ 8694656138029 := by decide +kernel

theorem rows22250R_3920 : rowsJ2 147 148 64 65 ≤ 7608674105027 := by decide +kernel

theorem rows22250R_3921 : rowsJ2 147 148 65 66 ≤ 6601106576881 := by decide +kernel

theorem rows22250R_3922 : rowsJ2 147 148 66 67 ≤ 5670238254116 := by decide +kernel

theorem rows22250R_3923 : rowsJ2 147 148 67 69 ≤ 8846910911573 := by decide +kernel

theorem rows22250R_3924 : rowsJ2 147 148 69 71 ≤ 6006862030750 := by decide +kernel

theorem rows22250R_3925 : rowsJ2 147 148 71 75 ≤ 5739254030454 := by decide +kernel

theorem rows22250R_3926 : rowsJ2 147 148 75 340 ≤ 1635447013913939 := by decide +kernel

theorem rows22250R_3927 : rowsJ2 148 149 0 44 ≤ 3177596244019 := by decide +kernel

theorem rows22250R_3928 : rowsJ2 148 149 44 48 ≤ 11040689535437 := by decide +kernel

theorem rows22250R_3929 : rowsJ2 148 149 48 50 ≤ 9820422917393 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3916
#print axioms SieveCert.rows22250R_3929
