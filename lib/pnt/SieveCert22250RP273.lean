/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3028–3040 of 5796

File 273 of 465: the parts `rows22250R_3028` … `rows22250R_3040` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96248 tests: row 103 columns 96–96, row 103 columns 97–97, row 103 columns
98–98, row 103 columns 99–99, row 103 columns 100–100, row 103 columns 101–101, row 103 columns 102–102, row 103
columns 103–359, row 104 columns 0–16, row 104 columns 17–25, row 104 columns 26–33, row 104 columns 34–36, row 104
columns 37–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_3028 : rowsJ2 103 104 96 97 ≤ 2525132837884 := by decide +kernel

theorem rows22250R_3029 : rowsJ2 103 104 97 98 ≤ 2751794468521 := by decide +kernel

theorem rows22250R_3030 : rowsJ2 103 104 98 99 ≤ 3059330554277 := by decide +kernel

theorem rows22250R_3031 : rowsJ2 103 104 99 100 ≤ 3400928616265 := by decide +kernel

theorem rows22250R_3032 : rowsJ2 103 104 100 101 ≤ 3827247421020 := by decide +kernel

theorem rows22250R_3033 : rowsJ2 103 104 101 102 ≤ 4289771642354 := by decide +kernel

theorem rows22250R_3034 : rowsJ2 103 104 102 103 ≤ 4840261338927 := by decide +kernel

theorem rows22250R_3035 : rowsJ2 103 104 103 360 ≤ 5429441211791 := by decide +kernel

theorem rows22250R_3036 : rowsJ2 104 105 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_3037 : rowsJ2 104 105 17 26 ≤ 0 := by decide +kernel

theorem rows22250R_3038 : rowsJ2 104 105 26 34 ≤ 2804507954563 := by decide +kernel

theorem rows22250R_3039 : rowsJ2 104 105 34 37 ≤ 10140917192735 := by decide +kernel

theorem rows22250R_3040 : rowsJ2 104 105 37 39 ≤ 13203335808288 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3028
#print axioms SieveCert.rows22250R_3040
