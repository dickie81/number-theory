/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4196–4210 of 5066

File 331 of 387: the parts `rows22240R_4196` … `rows22240R_4210` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98097 in units of a depth-4 test: row 146 columns 62–62, row 146
columns 63–63, row 146 columns 64–64, row 146 columns 65–65, row 146 columns 66–66, row 146 columns 67–67, row 146
columns 68–68, row 146 columns 69–69, row 146 columns 70–71, row 146 columns 72–74, row 146 columns 75–80, row 146
columns 81–339, row 147 columns 0–41, row 147 columns 42–47, row 147 columns 48–49), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4196 : rowsJ2 146 147 62 63 ≤ 12025557806763 := by decide +kernel

theorem rows22240R_4197 : rowsJ2 146 147 63 64 ≤ 10738674702656 := by decide +kernel

theorem rows22240R_4198 : rowsJ2 146 147 64 65 ≤ 9532951593081 := by decide +kernel

theorem rows22240R_4199 : rowsJ2 146 147 65 66 ≤ 8406382668601 := by decide +kernel

theorem rows22240R_4200 : rowsJ2 146 147 66 67 ≤ 7357099195467 := by decide +kernel

theorem rows22240R_4201 : rowsJ2 146 147 67 68 ≤ 6383368276378 := by decide +kernel

theorem rows22240R_4202 : rowsJ2 146 147 68 69 ≤ 5483591585722 := by decide +kernel

theorem rows22240R_4203 : rowsJ2 146 147 69 70 ≤ 4656295291971 := by decide +kernel

theorem rows22240R_4204 : rowsJ2 146 147 70 72 ≤ 7113963925880 := by decide +kernel

theorem rows22240R_4205 : rowsJ2 146 147 72 75 ≤ 6206410047803 := by decide +kernel

theorem rows22240R_4206 : rowsJ2 146 147 75 81 ≤ 2894325833696 := by decide +kernel

theorem rows22240R_4207 : rowsJ2 146 147 81 340 ≤ 1519849080123296 := by decide +kernel

theorem rows22240R_4208 : rowsJ2 147 148 0 42 ≤ 1332630862400 := by decide +kernel

theorem rows22240R_4209 : rowsJ2 147 148 42 48 ≤ 9829702261495 := by decide +kernel

theorem rows22240R_4210 : rowsJ2 147 148 48 50 ≤ 8034056642552 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4196
#print axioms SieveCert.rows22240R_4210
