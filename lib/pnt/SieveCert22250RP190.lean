/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2293–2303 of 4715

File 190 of 351: the parts `rows22250R_2293` … `rows22250R_2303` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 89949 in units of a depth-4 test: row 92 columns 73–76, row 92 columns
77–78, row 92 columns 79–79, row 92 columns 80–80, row 92 columns 81–81, row 92 columns 82–82, row 92 columns 83–83,
row 92 columns 84–84, row 92 columns 85–85, row 92 columns 86–86, row 92 columns 87–87), each a sum of refined costs
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

theorem rows22250R_2293 : rowsJ2 92 93 73 77 ≤ 114524629487 := by decide +kernel

theorem rows22250R_2294 : rowsJ2 92 93 77 79 ≤ 747865280483 := by decide +kernel

theorem rows22250R_2295 : rowsJ2 92 93 79 80 ≤ 793437577476 := by decide +kernel

theorem rows22250R_2296 : rowsJ2 92 93 80 81 ≤ 1161183969694 := by decide +kernel

theorem rows22250R_2297 : rowsJ2 92 93 81 82 ≤ 1607428118485 := by decide +kernel

theorem rows22250R_2298 : rowsJ2 92 93 82 83 ≤ 2193833327459 := by decide +kernel

theorem rows22250R_2299 : rowsJ2 92 93 83 84 ≤ 2949106150445 := by decide +kernel

theorem rows22250R_2300 : rowsJ2 92 93 84 85 ≤ 3868284638969 := by decide +kernel

theorem rows22250R_2301 : rowsJ2 92 93 85 86 ≤ 4884035465988 := by decide +kernel

theorem rows22250R_2302 : rowsJ2 92 93 86 87 ≤ 5687852155035 := by decide +kernel

theorem rows22250R_2303 : rowsJ2 92 93 87 88 ≤ 4999863317157 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2293
#print axioms SieveCert.rows22250R_2303
