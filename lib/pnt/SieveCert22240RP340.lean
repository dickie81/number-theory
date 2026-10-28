/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4321–4335 of 5066

File 340 of 387: the parts `rows22240R_4321` … `rows22240R_4335` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98235 in units of a depth-4 test: row 151 columns 59–59, row 151
columns 60–60, row 151 columns 61–61, row 151 columns 62–62, row 151 columns 63–63, row 151 columns 64–64, row 151
columns 65–65, row 151 columns 66–66, row 151 columns 67–68, row 151 columns 69–71, row 151 columns 72–339, row 152
columns 0–42, row 152 columns 43–45, row 152 columns 46–47, row 152 columns 48–48), each a sum of refined costs
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

theorem rows22240R_4321 : rowsJ2 151 152 59 60 ≤ 13794385598593 := by decide +kernel

theorem rows22240R_4322 : rowsJ2 151 152 60 61 ≤ 12347875416656 := by decide +kernel

theorem rows22240R_4323 : rowsJ2 151 152 61 62 ≤ 10991566952244 := by decide +kernel

theorem rows22240R_4324 : rowsJ2 151 152 62 63 ≤ 9723062773550 := by decide +kernel

theorem rows22240R_4325 : rowsJ2 151 152 63 64 ≤ 8540139720336 := by decide +kernel

theorem rows22240R_4326 : rowsJ2 151 152 64 65 ≤ 7440735901802 := by decide +kernel

theorem rows22240R_4327 : rowsJ2 151 152 65 66 ≤ 6422943652842 := by decide +kernel

theorem rows22240R_4328 : rowsJ2 151 152 66 67 ≤ 5484996600719 := by decide +kernel

theorem rows22240R_4329 : rowsJ2 151 152 67 69 ≤ 8467583352555 := by decide +kernel

theorem rows22240R_4330 : rowsJ2 151 152 69 72 ≤ 7577230401380 := by decide +kernel

theorem rows22240R_4331 : rowsJ2 151 152 72 340 ≤ 2031500531280644 := by decide +kernel

theorem rows22240R_4332 : rowsJ2 152 153 0 43 ≤ 4376260752705 := by decide +kernel

theorem rows22240R_4333 : rowsJ2 152 153 43 46 ≤ 8788833102429 := by decide +kernel

theorem rows22240R_4334 : rowsJ2 152 153 46 48 ≤ 9615495486810 := by decide +kernel

theorem rows22240R_4335 : rowsJ2 152 153 48 49 ≤ 6118447197476 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4321
#print axioms SieveCert.rows22240R_4335
