/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3122–3136 of 4715

File 245 of 351: the parts `rows22250R_3122` … `rows22250R_3136` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98284 tests: row 116 columns 94–95, row 116 columns 96–339, row 117 columns
0–26, row 117 columns 27–29, row 117 columns 30–31, row 117 columns 32–33, row 117 columns 34–36, row 117 columns
37–41, row 117 columns 42–55, row 117 columns 56–60, row 117 columns 61–62, row 117 columns 63–64, row 117 columns
65–66, row 117 columns 67–68, row 117 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3122 : rowsJ2 116 117 94 96 ≤ 22580845921609 := by decide +kernel

theorem rows22250R_3123 : rowsJ2 116 117 96 340 ≤ 1461334130913034 := by decide +kernel

theorem rows22250R_3124 : rowsJ2 117 118 0 27 ≤ 2006756420243 := by decide +kernel

theorem rows22250R_3125 : rowsJ2 117 118 27 30 ≤ 12532583492965 := by decide +kernel

theorem rows22250R_3126 : rowsJ2 117 118 30 32 ≤ 17354676423570 := by decide +kernel

theorem rows22250R_3127 : rowsJ2 117 118 32 34 ≤ 16392956031680 := by decide +kernel

theorem rows22250R_3128 : rowsJ2 117 118 34 37 ≤ 17113664072344 := by decide +kernel

theorem rows22250R_3129 : rowsJ2 117 118 37 42 ≤ 10317730700927 := by decide +kernel

theorem rows22250R_3130 : rowsJ2 117 118 42 56 ≤ 261418235112 := by decide +kernel

theorem rows22250R_3131 : rowsJ2 117 118 56 61 ≤ 3686381736893 := by decide +kernel

theorem rows22250R_3132 : rowsJ2 117 118 61 63 ≤ 3305818556988 := by decide +kernel

theorem rows22250R_3133 : rowsJ2 117 118 63 65 ≤ 3825830907511 := by decide +kernel

theorem rows22250R_3134 : rowsJ2 117 118 65 67 ≤ 3827733850053 := by decide +kernel

theorem rows22250R_3135 : rowsJ2 117 118 67 69 ≤ 3292344156356 := by decide +kernel

theorem rows22250R_3136 : rowsJ2 117 118 69 72 ≤ 2700670374723 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3122
#print axioms SieveCert.rows22250R_3136
