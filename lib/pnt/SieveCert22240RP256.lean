/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3113–3128 of 5066

File 256 of 387: the parts `rows22240R_3113` … `rows22240R_3128` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95037 in units of a depth-4 test: row 108 columns 63–69, row 108
columns 70–73, row 108 columns 74–76, row 108 columns 77–78, row 108 columns 79–80, row 108 columns 81–82, row 108
columns 83–84, row 108 columns 85–86, row 108 columns 87–88, row 108 columns 89–90, row 108 columns 91–92, row 108
columns 93–93, row 108 columns 94–94, row 108 columns 95–95, row 108 columns 96–96, row 108 columns 97–97), each a
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

theorem rows22240R_3113 : rowsJ2 108 109 63 70 ≤ 384611283951 := by decide +kernel

theorem rows22240R_3114 : rowsJ2 108 109 70 74 ≤ 0 := by decide +kernel

theorem rows22240R_3115 : rowsJ2 108 109 74 77 ≤ 53907715126 := by decide +kernel

theorem rows22240R_3116 : rowsJ2 108 109 77 79 ≤ 496309387374 := by decide +kernel

theorem rows22240R_3117 : rowsJ2 108 109 79 81 ≤ 1050242705390 := by decide +kernel

theorem rows22240R_3118 : rowsJ2 108 109 81 83 ≤ 929246933923 := by decide +kernel

theorem rows22240R_3119 : rowsJ2 108 109 83 85 ≤ 1344347261051 := by decide +kernel

theorem rows22240R_3120 : rowsJ2 108 109 85 87 ≤ 2357723858597 := by decide +kernel

theorem rows22240R_3121 : rowsJ2 108 109 87 89 ≤ 3994192583094 := by decide +kernel

theorem rows22240R_3122 : rowsJ2 108 109 89 91 ≤ 6283495926025 := by decide +kernel

theorem rows22240R_3123 : rowsJ2 108 109 91 93 ≤ 9259888493162 := by decide +kernel

theorem rows22240R_3124 : rowsJ2 108 109 93 94 ≤ 5975747969896 := by decide +kernel

theorem rows22240R_3125 : rowsJ2 108 109 94 95 ≤ 6971102959710 := by decide +kernel

theorem rows22240R_3126 : rowsJ2 108 109 95 96 ≤ 8081409819066 := by decide +kernel

theorem rows22240R_3127 : rowsJ2 108 109 96 97 ≤ 9258478940545 := by decide +kernel

theorem rows22240R_3128 : rowsJ2 108 109 97 98 ≤ 10557152702352 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3113
#print axioms SieveCert.rows22240R_3128
