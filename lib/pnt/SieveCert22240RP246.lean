/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2950–2965 of 5066

File 246 of 387: the parts `rows22240R_2950` … `rows22240R_2965` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97690 in units of a depth-4 test: row 104 columns 40–40, row 104
columns 41–41, row 104 columns 42–42, row 104 columns 43–43, row 104 columns 44–45, row 104 columns 46–47, row 104
columns 48–49, row 104 columns 50–52, row 104 columns 53–57, row 104 columns 58–65, row 104 columns 66–71, row 104
columns 72–75, row 104 columns 76–78, row 104 columns 79–79, row 104 columns 80–80, row 104 columns 81–81), each a
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

theorem rows22240R_2950 : rowsJ2 104 105 40 41 ≤ 14131160978854 := by decide +kernel

theorem rows22240R_2951 : rowsJ2 104 105 41 42 ≤ 12236970815352 := by decide +kernel

theorem rows22240R_2952 : rowsJ2 104 105 42 43 ≤ 10535889985283 := by decide +kernel

theorem rows22240R_2953 : rowsJ2 104 105 43 44 ≤ 9023303720300 := by decide +kernel

theorem rows22240R_2954 : rowsJ2 104 105 44 46 ≤ 13839487659400 := by decide +kernel

theorem rows22240R_2955 : rowsJ2 104 105 46 48 ≤ 8783387734906 := by decide +kernel

theorem rows22240R_2956 : rowsJ2 104 105 48 50 ≤ 4804504026018 := by decide +kernel

theorem rows22240R_2957 : rowsJ2 104 105 50 53 ≤ 2843593832468 := by decide +kernel

theorem rows22240R_2958 : rowsJ2 104 105 53 58 ≤ 374512224880 := by decide +kernel

theorem rows22240R_2959 : rowsJ2 104 105 58 66 ≤ 0 := by decide +kernel

theorem rows22240R_2960 : rowsJ2 104 105 66 72 ≤ 0 := by decide +kernel

theorem rows22240R_2961 : rowsJ2 104 105 72 76 ≤ 0 := by decide +kernel

theorem rows22240R_2962 : rowsJ2 104 105 76 79 ≤ 570495665480 := by decide +kernel

theorem rows22240R_2963 : rowsJ2 104 105 79 80 ≤ 582457380098 := by decide +kernel

theorem rows22240R_2964 : rowsJ2 104 105 80 81 ≤ 887536666596 := by decide +kernel

theorem rows22240R_2965 : rowsJ2 104 105 81 82 ≤ 1248672069880 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2950
#print axioms SieveCert.rows22240R_2965
