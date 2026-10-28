/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4294–4306 of 5066

File 338 of 387: the parts `rows22240R_4294` … `rows22240R_4306` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 97662 in units of a depth-4 test: row 150 columns 57–57, row 150
columns 58–58, row 150 columns 59–59, row 150 columns 60–60, row 150 columns 61–61, row 150 columns 62–62, row 150
columns 63–63, row 150 columns 64–64, row 150 columns 65–65, row 150 columns 66–66, row 150 columns 67–68, row 150
columns 69–70, row 150 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_4294 : rowsJ2 150 151 57 58 ≤ 14592968585453 := by decide +kernel

theorem rows22240R_4295 : rowsJ2 150 151 58 59 ≤ 15876250990242 := by decide +kernel

theorem rows22240R_4296 : rowsJ2 150 151 59 60 ≤ 14317024661534 := by decide +kernel

theorem rows22240R_4297 : rowsJ2 150 151 60 61 ≤ 12850136909521 := by decide +kernel

theorem rows22240R_4298 : rowsJ2 150 151 61 62 ≤ 11472999505137 := by decide +kernel

theorem rows22240R_4299 : rowsJ2 150 151 62 63 ≤ 10183196568223 := by decide +kernel

theorem rows22240R_4300 : rowsJ2 150 151 63 64 ≤ 8978480852791 := by decide +kernel

theorem rows22240R_4301 : rowsJ2 150 151 64 65 ≤ 7856770200413 := by decide +kernel

theorem rows22240R_4302 : rowsJ2 150 151 65 66 ≤ 6816135226804 := by decide +kernel

theorem rows22240R_4303 : rowsJ2 150 151 66 67 ≤ 5854792888544 := by decide +kernel

theorem rows22240R_4304 : rowsJ2 150 151 67 69 ≤ 9134624677827 := by decide +kernel

theorem rows22240R_4305 : rowsJ2 150 151 69 71 ≤ 6202186858950 := by decide +kernel

theorem rows22240R_4306 : rowsJ2 150 151 71 75 ≤ 5926454346929 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4294
#print axioms SieveCert.rows22240R_4306
