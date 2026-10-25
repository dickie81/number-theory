/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3070–3082 of 5796

File 276 of 465: the parts `rows22250R_3070` … `rows22250R_3082` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95314 tests: row 104 columns 90–90, row 104 columns 91–91, row 104 columns
92–92, row 104 columns 93–93, row 104 columns 94–94, row 104 columns 95–95, row 104 columns 96–96, row 104 columns
97–97, row 104 columns 98–98, row 104 columns 99–99, row 104 columns 100–100, row 104 columns 101–101, row 104
columns 102–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3070 : rowsJ2 104 105 90 91 ≤ 2083566845635 := by decide +kernel

theorem rows22250R_3071 : rowsJ2 104 105 91 92 ≤ 1969868524151 := by decide +kernel

theorem rows22250R_3072 : rowsJ2 104 105 92 93 ≤ 1929855851700 := by decide +kernel

theorem rows22250R_3073 : rowsJ2 104 105 93 94 ≤ 1951690792919 := by decide +kernel

theorem rows22250R_3074 : rowsJ2 104 105 94 95 ≤ 2051394813611 := by decide +kernel

theorem rows22250R_3075 : rowsJ2 104 105 95 96 ≤ 2216123644884 := by decide +kernel

theorem rows22250R_3076 : rowsJ2 104 105 96 97 ≤ 2425882352854 := by decide +kernel

theorem rows22250R_3077 : rowsJ2 104 105 97 98 ≤ 2702845259162 := by decide +kernel

theorem rows22250R_3078 : rowsJ2 104 105 98 99 ≤ 3027671519655 := by decide +kernel

theorem rows22250R_3079 : rowsJ2 104 105 99 100 ≤ 3423344975258 := by decide +kernel

theorem rows22250R_3080 : rowsJ2 104 105 100 101 ≤ 3869143627395 := by decide +kernel

theorem rows22250R_3081 : rowsJ2 104 105 101 102 ≤ 4388822285777 := by decide +kernel

theorem rows22250R_3082 : rowsJ2 104 105 102 103 ≤ 4961235598197 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3070
#print axioms SieveCert.rows22250R_3082
