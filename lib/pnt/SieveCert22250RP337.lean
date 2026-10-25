/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4026–4040 of 5796

File 337 of 465: the parts `rows22250R_4026` … `rows22250R_4040` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97138 tests: row 130 columns 69–69, row 130 columns 70–70, row 130 columns
71–71, row 130 columns 72–72, row 130 columns 73–73, row 130 columns 74–74, row 130 columns 75–75, row 130 columns
76–76, row 130 columns 77–77, row 130 columns 78–78, row 130 columns 79–80, row 130 columns 81–83, row 130 columns
84–87, row 130 columns 88–90, row 130 columns 91–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4026 : rowsJ2 130 131 69 70 ≤ 3874517843060 := by decide +kernel

theorem rows22250R_4027 : rowsJ2 130 131 70 71 ≤ 3976193967560 := by decide +kernel

theorem rows22250R_4028 : rowsJ2 130 131 71 72 ≤ 4016625581453 := by decide +kernel

theorem rows22250R_4029 : rowsJ2 130 131 72 73 ≤ 4013507876995 := by decide +kernel

theorem rows22250R_4030 : rowsJ2 130 131 73 74 ≤ 3946919341869 := by decide +kernel

theorem rows22250R_4031 : rowsJ2 130 131 74 75 ≤ 3834506498397 := by decide +kernel

theorem rows22250R_4032 : rowsJ2 130 131 75 76 ≤ 3655864159204 := by decide +kernel

theorem rows22250R_4033 : rowsJ2 130 131 76 77 ≤ 3063683071962 := by decide +kernel

theorem rows22250R_4034 : rowsJ2 130 131 77 78 ≤ 2503833467373 := by decide +kernel

theorem rows22250R_4035 : rowsJ2 130 131 78 79 ≤ 1994614284027 := by decide +kernel

theorem rows22250R_4036 : rowsJ2 130 131 79 81 ≤ 2600875243673 := by decide +kernel

theorem rows22250R_4037 : rowsJ2 130 131 81 84 ≤ 1011699436832 := by decide +kernel

theorem rows22250R_4038 : rowsJ2 130 131 84 88 ≤ 457698496971 := by decide +kernel

theorem rows22250R_4039 : rowsJ2 130 131 88 91 ≤ 4811970882407 := by decide +kernel

theorem rows22250R_4040 : rowsJ2 130 131 91 94 ≤ 11747668447178 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4026
#print axioms SieveCert.rows22250R_4040
