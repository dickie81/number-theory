/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3173–3188 of 5796

File 283 of 465: the parts `rows22250R_3173` … `rows22250R_3188` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96888 tests: row 106 columns 95–95, row 106 columns 96–96, row 106 columns
97–97, row 106 columns 98–98, row 106 columns 99–99, row 106 columns 100–100, row 106 columns 101–101, row 106
columns 102–102, row 106 columns 103–103, row 106 columns 104–104, row 106 columns 105–105, row 106 columns 106–359,
row 107 columns 0–17, row 107 columns 18–29, row 107 columns 30–33, row 107 columns 34–35), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3173 : rowsJ2 106 107 95 96 ≤ 2047520207604 := by decide +kernel

theorem rows22250R_3174 : rowsJ2 106 107 96 97 ≤ 2323683007458 := by decide +kernel

theorem rows22250R_3175 : rowsJ2 106 107 97 98 ≤ 2670894788781 := by decide +kernel

theorem rows22250R_3176 : rowsJ2 106 107 98 99 ≤ 3068031234977 := by decide +kernel

theorem rows22250R_3177 : rowsJ2 106 107 99 100 ≤ 3539158688571 := by decide +kernel

theorem rows22250R_3178 : rowsJ2 106 107 100 101 ≤ 4062725183656 := by decide +kernel

theorem rows22250R_3179 : rowsJ2 106 107 101 102 ≤ 4663617654320 := by decide +kernel

theorem rows22250R_3180 : rowsJ2 106 107 102 103 ≤ 5319843733441 := by decide +kernel

theorem rows22250R_3181 : rowsJ2 106 107 103 104 ≤ 6057163097100 := by decide +kernel

theorem rows22250R_3182 : rowsJ2 106 107 104 105 ≤ 6853131608100 := by decide +kernel

theorem rows22250R_3183 : rowsJ2 106 107 105 106 ≤ 7734439130134 := by decide +kernel

theorem rows22250R_3184 : rowsJ2 106 107 106 360 ≤ 8678180180559 := by decide +kernel

theorem rows22250R_3185 : rowsJ2 107 108 0 18 ≤ 0 := by decide +kernel

theorem rows22250R_3186 : rowsJ2 107 108 18 30 ≤ 0 := by decide +kernel

theorem rows22250R_3187 : rowsJ2 107 108 30 34 ≤ 4313421678122 := by decide +kernel

theorem rows22250R_3188 : rowsJ2 107 108 34 36 ≤ 7344804907298 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3173
#print axioms SieveCert.rows22250R_3188
