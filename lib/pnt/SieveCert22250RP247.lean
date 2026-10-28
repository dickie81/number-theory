/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3152–3166 of 4715

File 247 of 351: the parts `rows22250R_3152` … `rows22250R_3166` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 97960 in units of a depth-4 test: row 118 columns 39–47, row 118
columns 48–59, row 118 columns 60–61, row 118 columns 62–63, row 118 columns 64–65, row 118 columns 66–67, row 118
columns 68–69, row 118 columns 70–71, row 118 columns 72–74, row 118 columns 75–77, row 118 columns 78–81, row 118
columns 82–84, row 118 columns 85–87, row 118 columns 88–89, row 118 columns 90–91), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3152 : rowsJ2 118 119 39 48 ≤ 2359060729243 := by decide +kernel

theorem rows22250R_3153 : rowsJ2 118 119 48 60 ≤ 3142185804645 := by decide +kernel

theorem rows22250R_3154 : rowsJ2 118 119 60 62 ≤ 3277783641859 := by decide +kernel

theorem rows22250R_3155 : rowsJ2 118 119 62 64 ≤ 4159887101935 := by decide +kernel

theorem rows22250R_3156 : rowsJ2 118 119 64 66 ≤ 4533802927222 := by decide +kernel

theorem rows22250R_3157 : rowsJ2 118 119 66 68 ≤ 4383174785531 := by decide +kernel

theorem rows22250R_3158 : rowsJ2 118 119 68 70 ≤ 3686661059159 := by decide +kernel

theorem rows22250R_3159 : rowsJ2 118 119 70 72 ≤ 2417263761607 := by decide +kernel

theorem rows22250R_3160 : rowsJ2 118 119 72 75 ≤ 541464410137 := by decide +kernel

theorem rows22250R_3161 : rowsJ2 118 119 75 78 ≤ 0 := by decide +kernel

theorem rows22250R_3162 : rowsJ2 118 119 78 82 ≤ 0 := by decide +kernel

theorem rows22250R_3163 : rowsJ2 118 119 82 85 ≤ 2311741483144 := by decide +kernel

theorem rows22250R_3164 : rowsJ2 118 119 85 88 ≤ 7695290072748 := by decide +kernel

theorem rows22250R_3165 : rowsJ2 118 119 88 90 ≤ 9368965661170 := by decide +kernel

theorem rows22250R_3166 : rowsJ2 118 119 90 92 ≤ 13715330129508 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3152
#print axioms SieveCert.rows22250R_3166
