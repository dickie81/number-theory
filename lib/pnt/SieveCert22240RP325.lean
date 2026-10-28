/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4117–4129 of 5066

File 325 of 387: the parts `rows22240R_4117` … `rows22240R_4129` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 97170 in units of a depth-4 test: row 143 columns 62–62, row 143
columns 63–63, row 143 columns 64–64, row 143 columns 65–65, row 143 columns 66–66, row 143 columns 67–67, row 143
columns 68–68, row 143 columns 69–69, row 143 columns 70–70, row 143 columns 71–72, row 143 columns 73–74, row 143
columns 75–78, row 143 columns 79–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4117 : rowsJ2 143 144 62 63 ≤ 13397307441994 := by decide +kernel

theorem rows22240R_4118 : rowsJ2 143 144 63 64 ≤ 12072668929929 := by decide +kernel

theorem rows22240R_4119 : rowsJ2 143 144 64 65 ≤ 10828430141129 := by decide +kernel

theorem rows22240R_4120 : rowsJ2 143 144 65 66 ≤ 9642283514760 := by decide +kernel

theorem rows22240R_4121 : rowsJ2 143 144 66 67 ≤ 8532127593990 := by decide +kernel

theorem rows22240R_4122 : rowsJ2 143 144 67 68 ≤ 7496179943738 := by decide +kernel

theorem rows22240R_4123 : rowsJ2 143 144 68 69 ≤ 6532785238399 := by decide +kernel

theorem rows22240R_4124 : rowsJ2 143 144 69 70 ≤ 5640404928291 := by decide +kernel

theorem rows22240R_4125 : rowsJ2 143 144 70 71 ≤ 4817617359275 := by decide +kernel

theorem rows22240R_4126 : rowsJ2 143 144 71 73 ≤ 7438827223929 := by decide +kernel

theorem rows22240R_4127 : rowsJ2 143 144 73 75 ≤ 4952194579509 := by decide +kernel

theorem rows22240R_4128 : rowsJ2 143 144 75 79 ≤ 4498465402812 := by decide +kernel

theorem rows22240R_4129 : rowsJ2 143 144 79 340 ≤ 1228591387579916 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4117
#print axioms SieveCert.rows22240R_4129
