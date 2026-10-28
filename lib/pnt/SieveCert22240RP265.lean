/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3254–3267 of 5066

File 265 of 387: the parts `rows22240R_3254` … `rows22240R_3267` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99141 in units of a depth-4 test: row 113 columns 26–30, row 113
columns 31–32, row 113 columns 33–34, row 113 columns 35–36, row 113 columns 37–38, row 113 columns 39–40, row 113
columns 41–43, row 113 columns 44–48, row 113 columns 49–59, row 113 columns 60–63, row 113 columns 64–66, row 113
columns 67–70, row 113 columns 71–74, row 113 columns 75–77), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3254 : rowsJ2 113 114 26 31 ≤ 9873289544295 := by decide +kernel

theorem rows22240R_3255 : rowsJ2 113 114 31 33 ≤ 13116162929263 := by decide +kernel

theorem rows22240R_3256 : rowsJ2 113 114 33 35 ≤ 21415801778883 := by decide +kernel

theorem rows22240R_3257 : rowsJ2 113 114 35 37 ≤ 24248085123125 := by decide +kernel

theorem rows22240R_3258 : rowsJ2 113 114 37 39 ≤ 19138206135144 := by decide +kernel

theorem rows22240R_3259 : rowsJ2 113 114 39 41 ≤ 12600711668552 := by decide +kernel

theorem rows22240R_3260 : rowsJ2 113 114 41 44 ≤ 10170016863462 := by decide +kernel

theorem rows22240R_3261 : rowsJ2 113 114 44 49 ≤ 3790447182408 := by decide +kernel

theorem rows22240R_3262 : rowsJ2 113 114 49 60 ≤ 540598121597 := by decide +kernel

theorem rows22240R_3263 : rowsJ2 113 114 60 64 ≤ 3262680526662 := by decide +kernel

theorem rows22240R_3264 : rowsJ2 113 114 64 67 ≤ 3166429860572 := by decide +kernel

theorem rows22240R_3265 : rowsJ2 113 114 67 71 ≤ 1830167934973 := by decide +kernel

theorem rows22240R_3266 : rowsJ2 113 114 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_3267 : rowsJ2 113 114 75 78 ≤ 128882604769 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3254
#print axioms SieveCert.rows22240R_3267
