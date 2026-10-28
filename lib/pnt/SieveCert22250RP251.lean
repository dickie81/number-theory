/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3213–3228 of 4715

File 251 of 351: the parts `rows22250R_3213` … `rows22250R_3228` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96635 in units of a depth-4 test: row 120 columns 90–91, row 120
columns 92–93, row 120 columns 94–339, row 121 columns 0–25, row 121 columns 26–28, row 121 columns 29–31, row 121
columns 32–35, row 121 columns 36–44, row 121 columns 45–57, row 121 columns 58–60, row 121 columns 61–62, row 121
columns 63–63, row 121 columns 64–64, row 121 columns 65–65, row 121 columns 66–66, row 121 columns 67–67), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3213 : rowsJ2 120 121 90 92 ≤ 15396338535614 := by decide +kernel

theorem rows22250R_3214 : rowsJ2 120 121 92 94 ≤ 21121700513825 := by decide +kernel

theorem rows22250R_3215 : rowsJ2 120 121 94 340 ≤ 1230156228690500 := by decide +kernel

theorem rows22250R_3216 : rowsJ2 121 122 0 26 ≤ 2716424320194 := by decide +kernel

theorem rows22250R_3217 : rowsJ2 121 122 26 29 ≤ 12809680636164 := by decide +kernel

theorem rows22250R_3218 : rowsJ2 121 122 29 32 ≤ 20519862411457 := by decide +kernel

theorem rows22250R_3219 : rowsJ2 121 122 32 36 ≤ 15533476086633 := by decide +kernel

theorem rows22250R_3220 : rowsJ2 121 122 36 45 ≤ 6010497993563 := by decide +kernel

theorem rows22250R_3221 : rowsJ2 121 122 45 58 ≤ 2678002201655 := by decide +kernel

theorem rows22250R_3222 : rowsJ2 121 122 58 61 ≤ 5400822171217 := by decide +kernel

theorem rows22250R_3223 : rowsJ2 121 122 61 63 ≤ 5464765238468 := by decide +kernel

theorem rows22250R_3224 : rowsJ2 121 122 63 64 ≤ 3127622370870 := by decide +kernel

theorem rows22250R_3225 : rowsJ2 121 122 64 65 ≤ 3299475950025 := by decide +kernel

theorem rows22250R_3226 : rowsJ2 121 122 65 66 ≤ 3419103327357 := by decide +kernel

theorem rows22250R_3227 : rowsJ2 121 122 66 67 ≤ 3461798803263 := by decide +kernel

theorem rows22250R_3228 : rowsJ2 121 122 67 68 ≤ 3450057906869 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3213
#print axioms SieveCert.rows22250R_3228
