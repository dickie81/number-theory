/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3404–3417 of 5066

File 275 of 387: the parts `rows22240R_3404` … `rows22240R_3417` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 93160 in units of a depth-4 test: row 118 columns 87–88, row 118
columns 89–90, row 118 columns 91–92, row 118 columns 93–94, row 118 columns 95–339, row 119 columns 0–26, row 119
columns 27–29, row 119 columns 30–31, row 119 columns 32–33, row 119 columns 34–36, row 119 columns 37–40, row 119
columns 41–49, row 119 columns 50–59, row 119 columns 60–61), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3404 : rowsJ2 118 119 87 89 ≤ 8596743209289 := by decide +kernel

theorem rows22240R_3405 : rowsJ2 118 119 89 91 ≤ 12631792937153 := by decide +kernel

theorem rows22240R_3406 : rowsJ2 118 119 91 93 ≤ 17495513538978 := by decide +kernel

theorem rows22240R_3407 : rowsJ2 118 119 93 95 ≤ 23248703488178 := by decide +kernel

theorem rows22240R_3408 : rowsJ2 118 119 95 340 ≤ 1435559382939871 := by decide +kernel

theorem rows22240R_3409 : rowsJ2 119 120 0 27 ≤ 1524752500689 := by decide +kernel

theorem rows22240R_3410 : rowsJ2 119 120 27 30 ≤ 11226570858916 := by decide +kernel

theorem rows22240R_3411 : rowsJ2 119 120 30 32 ≤ 16061419074512 := by decide +kernel

theorem rows22240R_3412 : rowsJ2 119 120 32 34 ≤ 18414856129754 := by decide +kernel

theorem rows22240R_3413 : rowsJ2 119 120 34 37 ≤ 19852604733161 := by decide +kernel

theorem rows22240R_3414 : rowsJ2 119 120 37 41 ≤ 12182281180814 := by decide +kernel

theorem rows22240R_3415 : rowsJ2 119 120 41 50 ≤ 1249146900043 := by decide +kernel

theorem rows22240R_3416 : rowsJ2 119 120 50 60 ≤ 3162664053622 := by decide +kernel

theorem rows22240R_3417 : rowsJ2 119 120 60 62 ≤ 3441962450870 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3404
#print axioms SieveCert.rows22240R_3417
