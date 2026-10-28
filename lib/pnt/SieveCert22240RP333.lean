/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4223–4238 of 5066

File 333 of 387: the parts `rows22240R_4223` … `rows22240R_4238` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98436 in units of a depth-4 test: row 147 columns 63–63, row 147
columns 64–64, row 147 columns 65–65, row 147 columns 66–66, row 147 columns 67–67, row 147 columns 68–68, row 147
columns 69–70, row 147 columns 71–72, row 147 columns 73–76, row 147 columns 77–339, row 148 columns 0–42, row 148
columns 43–47, row 148 columns 48–49, row 148 columns 50–50, row 148 columns 51–51, row 148 columns 52–52), each a
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

theorem rows22240R_4223 : rowsJ2 147 148 63 64 ≤ 10282817714337 := by decide +kernel

theorem rows22240R_4224 : rowsJ2 147 148 64 65 ≤ 9097494526361 := by decide +kernel

theorem rows22240R_4225 : rowsJ2 147 148 65 66 ≤ 7991771249198 := by decide +kernel

theorem rows22240R_4226 : rowsJ2 147 148 66 67 ≤ 6963798156652 := by decide +kernel

theorem rows22240R_4227 : rowsJ2 147 148 67 68 ≤ 6011866892213 := by decide +kernel

theorem rows22240R_4228 : rowsJ2 147 148 68 69 ≤ 5134399900651 := by decide +kernel

theorem rows22240R_4229 : rowsJ2 147 148 69 71 ≤ 7927112756249 := by decide +kernel

theorem rows22240R_4230 : rowsJ2 147 148 71 73 ≤ 5276757155814 := by decide +kernel

theorem rows22240R_4231 : rowsJ2 147 148 73 77 ≤ 4793380371802 := by decide +kernel

theorem rows22240R_4232 : rowsJ2 147 148 77 340 ≤ 1544209276645305 := by decide +kernel

theorem rows22240R_4233 : rowsJ2 148 149 0 43 ≤ 2028054027981 := by decide +kernel

theorem rows22240R_4234 : rowsJ2 148 149 43 48 ≤ 10875006200377 := by decide +kernel

theorem rows22240R_4235 : rowsJ2 148 149 48 50 ≤ 8961022724562 := by decide +kernel

theorem rows22240R_4236 : rowsJ2 148 149 50 51 ≤ 5704535430241 := by decide +kernel

theorem rows22240R_4237 : rowsJ2 148 149 51 52 ≤ 6591388708452 := by decide +kernel

theorem rows22240R_4238 : rowsJ2 148 149 52 53 ≤ 7528661368491 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4223
#print axioms SieveCert.rows22240R_4238
