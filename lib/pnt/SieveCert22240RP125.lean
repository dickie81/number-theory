/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1297–1307 of 5066

File 125 of 387: the parts `rows22240R_1297` … `rows22240R_1307` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 94983 in units of a depth-4 test: row 68 columns 62–62, row 68 columns
63–63, row 68 columns 64–64, row 68 columns 65–65, row 68 columns 66–66, row 68 columns 67–67, row 68 columns
68–339, row 69 columns 0–17, row 69 columns 18–20, row 69 columns 21–22, row 69 columns 23–23), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1297 : rowsJ2 68 69 62 63 ≤ 6228907622633 := by decide +kernel

theorem rows22240R_1298 : rowsJ2 68 69 63 64 ≤ 5830711592378 := by decide +kernel

theorem rows22240R_1299 : rowsJ2 68 69 64 65 ≤ 5488656432987 := by decide +kernel

theorem rows22240R_1300 : rowsJ2 68 69 65 66 ≤ 5084391453715 := by decide +kernel

theorem rows22240R_1301 : rowsJ2 68 69 66 67 ≤ 4736775416943 := by decide +kernel

theorem rows22240R_1302 : rowsJ2 68 69 67 68 ≤ 4325486542489 := by decide +kernel

theorem rows22240R_1303 : rowsJ2 68 69 68 340 ≤ 3971399629019 := by decide +kernel

theorem rows22240R_1304 : rowsJ2 69 70 0 18 ≤ 1640491488069 := by decide +kernel

theorem rows22240R_1305 : rowsJ2 69 70 18 21 ≤ 51388360783 := by decide +kernel

theorem rows22240R_1306 : rowsJ2 69 70 21 23 ≤ 4258789196 := by decide +kernel

theorem rows22240R_1307 : rowsJ2 69 70 23 24 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1297
#print axioms SieveCert.rows22240R_1307
