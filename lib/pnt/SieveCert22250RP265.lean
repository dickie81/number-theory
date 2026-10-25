/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2925–2933 of 5796

File 265 of 465: the parts `rows22250R_2925` … `rows22250R_2933` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93749 tests: row 101 columns 90–90, row 101 columns 91–91, row 101 columns
92–92, row 101 columns 93–93, row 101 columns 94–94, row 101 columns 95–95, row 101 columns 96–96, row 101 columns
97–97, row 101 columns 98–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2925 : rowsJ2 101 102 90 91 ≤ 3177463004254 := by decide +kernel

theorem rows22250R_2926 : rowsJ2 101 102 91 92 ≤ 3000829582192 := by decide +kernel

theorem rows22250R_2927 : rowsJ2 101 102 92 93 ≤ 2834859985971 := by decide +kernel

theorem rows22250R_2928 : rowsJ2 101 102 93 94 ≤ 2727083105426 := by decide +kernel

theorem rows22250R_2929 : rowsJ2 101 102 94 95 ≤ 2691344137289 := by decide +kernel

theorem rows22250R_2930 : rowsJ2 101 102 95 96 ≤ 2715355563824 := by decide +kernel

theorem rows22250R_2931 : rowsJ2 101 102 96 97 ≤ 2814440933408 := by decide +kernel

theorem rows22250R_2932 : rowsJ2 101 102 97 98 ≤ 2977453996138 := by decide +kernel

theorem rows22250R_2933 : rowsJ2 101 102 98 99 ≤ 3219006821454 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2925
#print axioms SieveCert.rows22250R_2933
