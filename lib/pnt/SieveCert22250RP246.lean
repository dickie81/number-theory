/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3137–3151 of 4715

File 246 of 351: the parts `rows22250R_3137` … `rows22250R_3151` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95029 tests: row 117 columns 72–74, row 117 columns 75–77, row 117 columns
78–81, row 117 columns 82–84, row 117 columns 85–87, row 117 columns 88–89, row 117 columns 90–91, row 117 columns
92–93, row 117 columns 94–101, row 117 columns 102–339, row 118 columns 0–26, row 118 columns 27–29, row 118 columns
30–31, row 118 columns 32–34, row 118 columns 35–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3137 : rowsJ2 117 118 72 75 ≤ 0 := by decide +kernel

theorem rows22250R_3138 : rowsJ2 117 118 75 78 ≤ 0 := by decide +kernel

theorem rows22250R_3139 : rowsJ2 117 118 78 82 ≤ 0 := by decide +kernel

theorem rows22250R_3140 : rowsJ2 117 118 82 85 ≤ 2163012415023 := by decide +kernel

theorem rows22250R_3141 : rowsJ2 117 118 85 88 ≤ 7174995728717 := by decide +kernel

theorem rows22250R_3142 : rowsJ2 117 118 88 90 ≤ 8805619289990 := by decide +kernel

theorem rows22250R_3143 : rowsJ2 117 118 90 92 ≤ 12944529698410 := by decide +kernel

theorem rows22250R_3144 : rowsJ2 117 118 92 94 ≤ 17936986430976 := by decide +kernel

theorem rows22250R_3145 : rowsJ2 117 118 94 102 ≤ 628490647899622 := by decide +kernel

theorem rows22250R_3146 : rowsJ2 117 118 102 340 ≤ 836114768972102 := by decide +kernel

theorem rows22250R_3147 : rowsJ2 118 119 0 27 ≤ 2741919925197 := by decide +kernel

theorem rows22250R_3148 : rowsJ2 118 119 27 30 ≤ 13717754531942 := by decide +kernel

theorem rows22250R_3149 : rowsJ2 118 119 30 32 ≤ 17005071110474 := by decide +kernel

theorem rows22250R_3150 : rowsJ2 118 119 32 35 ≤ 20108638330356 := by decide +kernel

theorem rows22250R_3151 : rowsJ2 118 119 35 39 ≤ 14732396344978 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3137
#print axioms SieveCert.rows22250R_3151
