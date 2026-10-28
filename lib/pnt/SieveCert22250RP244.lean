/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3108–3121 of 4715

File 244 of 351: the parts `rows22250R_3108` … `rows22250R_3121` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 94960 in units of a depth-4 test: row 116 columns 41–49, row 116
columns 50–60, row 116 columns 61–63, row 116 columns 64–65, row 116 columns 66–67, row 116 columns 68–70, row 116
columns 71–73, row 116 columns 74–76, row 116 columns 77–79, row 116 columns 80–83, row 116 columns 84–86, row 116
columns 87–89, row 116 columns 90–91, row 116 columns 92–93), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_3108 : rowsJ2 116 117 41 50 ≤ 1249324324085 := by decide +kernel

theorem rows22250R_3109 : rowsJ2 116 117 50 61 ≤ 3035565259310 := by decide +kernel

theorem rows22250R_3110 : rowsJ2 116 117 61 64 ≤ 4441315079186 := by decide +kernel

theorem rows22250R_3111 : rowsJ2 116 117 64 66 ≤ 3257666379772 := by decide +kernel

theorem rows22250R_3112 : rowsJ2 116 117 66 68 ≤ 2881397897673 := by decide +kernel

theorem rows22250R_3113 : rowsJ2 116 117 68 71 ≤ 2398975604068 := by decide +kernel

theorem rows22250R_3114 : rowsJ2 116 117 71 74 ≤ 0 := by decide +kernel

theorem rows22250R_3115 : rowsJ2 116 117 74 77 ≤ 0 := by decide +kernel

theorem rows22250R_3116 : rowsJ2 116 117 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_3117 : rowsJ2 116 117 80 84 ≤ 878350479951 := by decide +kernel

theorem rows22250R_3118 : rowsJ2 116 117 84 87 ≤ 4789338494550 := by decide +kernel

theorem rows22250R_3119 : rowsJ2 116 117 87 90 ≤ 11097643693241 := by decide +kernel

theorem rows22250R_3120 : rowsJ2 116 117 90 92 ≤ 12156381005190 := by decide +kernel

theorem rows22250R_3121 : rowsJ2 116 117 92 94 ≤ 16924510598573 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3108
#print axioms SieveCert.rows22250R_3121
