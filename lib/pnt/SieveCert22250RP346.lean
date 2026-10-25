/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4159–4173 of 5796

File 346 of 465: the parts `rows22250R_4159` … `rows22250R_4173` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97932 tests: row 134 columns 74–74, row 134 columns 75–75, row 134 columns
76–76, row 134 columns 77–77, row 134 columns 78–78, row 134 columns 79–79, row 134 columns 80–80, row 134 columns
81–82, row 134 columns 83–85, row 134 columns 86–89, row 134 columns 90–92, row 134 columns 93–94, row 134 columns
95–359, row 135 columns 0–25, row 135 columns 26–28), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4159 : rowsJ2 134 135 74 75 ≤ 5276279375601 := by decide +kernel

theorem rows22250R_4160 : rowsJ2 134 135 75 76 ≤ 4628296998726 := by decide +kernel

theorem rows22250R_4161 : rowsJ2 134 135 76 77 ≤ 4032894678058 := by decide +kernel

theorem rows22250R_4162 : rowsJ2 134 135 77 78 ≤ 3470153069732 := by decide +kernel

theorem rows22250R_4163 : rowsJ2 134 135 78 79 ≤ 2957953697797 := by decide +kernel

theorem rows22250R_4164 : rowsJ2 134 135 79 80 ≤ 2476257550784 := by decide +kernel

theorem rows22250R_4165 : rowsJ2 134 135 80 81 ≤ 2043290871159 := by decide +kernel

theorem rows22250R_4166 : rowsJ2 134 135 81 83 ≤ 2920449327795 := by decide +kernel

theorem rows22250R_4167 : rowsJ2 134 135 83 86 ≤ 2023918702639 := by decide +kernel

theorem rows22250R_4168 : rowsJ2 134 135 86 90 ≤ 4034963900680 := by decide +kernel

theorem rows22250R_4169 : rowsJ2 134 135 90 93 ≤ 11443937020010 := by decide +kernel

theorem rows22250R_4170 : rowsJ2 134 135 93 95 ≤ 13150987756301 := by decide +kernel

theorem rows22250R_4171 : rowsJ2 134 135 95 360 ≤ 813951185479310 := by decide +kernel

theorem rows22250R_4172 : rowsJ2 135 136 0 26 ≤ 2888005609516 := by decide +kernel

theorem rows22250R_4173 : rowsJ2 135 136 26 29 ≤ 10447433335279 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4159
#print axioms SieveCert.rows22250R_4173
