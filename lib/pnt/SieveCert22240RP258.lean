/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3145–3160 of 5066

File 258 of 387: the parts `rows22240R_3145` … `rows22240R_3160` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96618 in units of a depth-4 test: row 109 columns 53–61, row 109
columns 62–67, row 109 columns 68–72, row 109 columns 73–75, row 109 columns 76–77, row 109 columns 78–79, row 109
columns 80–81, row 109 columns 82–83, row 109 columns 84–85, row 109 columns 86–87, row 109 columns 88–89, row 109
columns 90–91, row 109 columns 92–93, row 109 columns 94–94, row 109 columns 95–95, row 109 columns 96–96), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3145 : rowsJ2 109 110 53 62 ≤ 490149537544 := by decide +kernel

theorem rows22240R_3146 : rowsJ2 109 110 62 68 ≤ 1208504303794 := by decide +kernel

theorem rows22240R_3147 : rowsJ2 109 110 68 73 ≤ 0 := by decide +kernel

theorem rows22240R_3148 : rowsJ2 109 110 73 76 ≤ 0 := by decide +kernel

theorem rows22240R_3149 : rowsJ2 109 110 76 78 ≤ 212999489159 := by decide +kernel

theorem rows22240R_3150 : rowsJ2 109 110 78 80 ≤ 733009248330 := by decide +kernel

theorem rows22240R_3151 : rowsJ2 109 110 80 82 ≤ 653398094835 := by decide +kernel

theorem rows22240R_3152 : rowsJ2 109 110 82 84 ≤ 923671130317 := by decide +kernel

theorem rows22240R_3153 : rowsJ2 109 110 84 86 ≤ 1793882131385 := by decide +kernel

theorem rows22240R_3154 : rowsJ2 109 110 86 88 ≤ 3288239545032 := by decide +kernel

theorem rows22240R_3155 : rowsJ2 109 110 88 90 ≤ 5435873341408 := by decide +kernel

theorem rows22240R_3156 : rowsJ2 109 110 90 92 ≤ 8270415447954 := by decide +kernel

theorem rows22240R_3157 : rowsJ2 109 110 92 94 ≤ 11783847233110 := by decide +kernel

theorem rows22240R_3158 : rowsJ2 109 110 94 95 ≤ 7434191809915 := by decide +kernel

theorem rows22240R_3159 : rowsJ2 109 110 95 96 ≤ 8567004885562 := by decide +kernel

theorem rows22240R_3160 : rowsJ2 109 110 96 97 ≤ 9821053420264 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3145
#print axioms SieveCert.rows22240R_3160
