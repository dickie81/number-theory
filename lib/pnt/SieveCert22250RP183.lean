/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2203–2216 of 4715

File 183 of 351: the parts `rows22250R_2203` … `rows22250R_2216` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 90801 in units of a depth-4 test: row 90 columns 53–53, row 90 columns
54–54, row 90 columns 55–56, row 90 columns 57–58, row 90 columns 59–60, row 90 columns 61–63, row 90 columns 64–68,
row 90 columns 69–73, row 90 columns 74–77, row 90 columns 78–79, row 90 columns 80–80, row 90 columns 81–81, row 90
columns 82–82, row 90 columns 83–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2203 : rowsJ2 90 91 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2204 : rowsJ2 90 91 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2205 : rowsJ2 90 91 55 57 ≤ 0 := by decide +kernel

theorem rows22250R_2206 : rowsJ2 90 91 57 59 ≤ 0 := by decide +kernel

theorem rows22250R_2207 : rowsJ2 90 91 59 61 ≤ 0 := by decide +kernel

theorem rows22250R_2208 : rowsJ2 90 91 61 64 ≤ 0 := by decide +kernel

theorem rows22250R_2209 : rowsJ2 90 91 64 69 ≤ 0 := by decide +kernel

theorem rows22250R_2210 : rowsJ2 90 91 69 74 ≤ 0 := by decide +kernel

theorem rows22250R_2211 : rowsJ2 90 91 74 78 ≤ 380738647237 := by decide +kernel

theorem rows22250R_2212 : rowsJ2 90 91 78 80 ≤ 1299255833584 := by decide +kernel

theorem rows22250R_2213 : rowsJ2 90 91 80 81 ≤ 1179506955041 := by decide +kernel

theorem rows22250R_2214 : rowsJ2 90 91 81 82 ≤ 1631998544561 := by decide +kernel

theorem rows22250R_2215 : rowsJ2 90 91 82 83 ≤ 2221943906641 := by decide +kernel

theorem rows22250R_2216 : rowsJ2 90 91 83 84 ≤ 2975874906504 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2203
#print axioms SieveCert.rows22250R_2216
