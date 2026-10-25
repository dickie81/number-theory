/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3963–3978 of 5796

File 333 of 465: the parts `rows22250R_3963` … `rows22250R_3978` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94627 tests: row 128 columns 70–70, row 128 columns 71–71, row 128 columns
72–72, row 128 columns 73–73, row 128 columns 74–74, row 128 columns 75–75, row 128 columns 76–76, row 128 columns
77–77, row 128 columns 78–79, row 128 columns 80–82, row 128 columns 83–85, row 128 columns 86–88, row 128 columns
89–91, row 128 columns 92–93, row 128 columns 94–95, row 128 columns 96–97), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3963 : rowsJ2 128 129 70 71 ≤ 3212580427273 := by decide +kernel

theorem rows22250R_3964 : rowsJ2 128 129 71 72 ≤ 3205886714768 := by decide +kernel

theorem rows22250R_3965 : rowsJ2 128 129 72 73 ≤ 3155132540205 := by decide +kernel

theorem rows22250R_3966 : rowsJ2 128 129 73 74 ≤ 3040142467855 := by decide +kernel

theorem rows22250R_3967 : rowsJ2 128 129 74 75 ≤ 2878731346106 := by decide +kernel

theorem rows22250R_3968 : rowsJ2 128 129 75 76 ≤ 2650233875389 := by decide +kernel

theorem rows22250R_3969 : rowsJ2 128 129 76 77 ≤ 2372389126936 := by decide +kernel

theorem rows22250R_3970 : rowsJ2 128 129 77 78 ≤ 1814238413639 := by decide +kernel

theorem rows22250R_3971 : rowsJ2 128 129 78 80 ≤ 2136027619110 := by decide +kernel

theorem rows22250R_3972 : rowsJ2 128 129 80 83 ≤ 400626648731 := by decide +kernel

theorem rows22250R_3973 : rowsJ2 128 129 83 86 ≤ 0 := by decide +kernel

theorem rows22250R_3974 : rowsJ2 128 129 86 89 ≤ 1245521377191 := by decide +kernel

theorem rows22250R_3975 : rowsJ2 128 129 89 92 ≤ 6087477637175 := by decide +kernel

theorem rows22250R_3976 : rowsJ2 128 129 92 94 ≤ 7789673347280 := by decide +kernel

theorem rows22250R_3977 : rowsJ2 128 129 94 96 ≤ 11570703239425 := by decide +kernel

theorem rows22250R_3978 : rowsJ2 128 129 96 98 ≤ 16084199450532 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3963
#print axioms SieveCert.rows22250R_3978
