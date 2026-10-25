/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2285–2300 of 5796

File 214 of 465: the parts `rows22250R_2285` … `rows22250R_2300` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98510 tests: row 88 columns 59–59, row 88 columns 60–60, row 88 columns
61–61, row 88 columns 62–62, row 88 columns 63–63, row 88 columns 64–64, row 88 columns 65–65, row 88 columns 66–66,
row 88 columns 67–67, row 88 columns 68–69, row 88 columns 70–71, row 88 columns 72–73, row 88 columns 74–76, row 88
columns 77–79, row 88 columns 80–81, row 88 columns 82–83), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2285 : rowsJ2 88 89 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2286 : rowsJ2 88 89 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2287 : rowsJ2 88 89 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2288 : rowsJ2 88 89 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2289 : rowsJ2 88 89 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2290 : rowsJ2 88 89 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_2291 : rowsJ2 88 89 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_2292 : rowsJ2 88 89 66 67 ≤ 0 := by decide +kernel

theorem rows22250R_2293 : rowsJ2 88 89 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_2294 : rowsJ2 88 89 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_2295 : rowsJ2 88 89 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_2296 : rowsJ2 88 89 72 74 ≤ 0 := by decide +kernel

theorem rows22250R_2297 : rowsJ2 88 89 74 77 ≤ 0 := by decide +kernel

theorem rows22250R_2298 : rowsJ2 88 89 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_2299 : rowsJ2 88 89 80 82 ≤ 222651168401 := by decide +kernel

theorem rows22250R_2300 : rowsJ2 88 89 82 84 ≤ 1116358795148 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2285
#print axioms SieveCert.rows22250R_2300
