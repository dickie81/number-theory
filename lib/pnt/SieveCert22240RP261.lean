/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3193–3207 of 5066

File 261 of 387: the parts `rows22240R_3193` … `rows22240R_3207` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94372 in units of a depth-4 test: row 110 columns 97–97, row 110
columns 98–98, row 110 columns 99–339, row 111 columns 0–25, row 111 columns 26–30, row 111 columns 31–32, row 111
columns 33–34, row 111 columns 35–35, row 111 columns 36–36, row 111 columns 37–38, row 111 columns 39–40, row 111
columns 41–42, row 111 columns 43–45, row 111 columns 46–50, row 111 columns 51–60), each a sum of refined costs
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

theorem rows22240R_3193 : rowsJ2 110 111 97 98 ≤ 11805260093801 := by decide +kernel

theorem rows22240R_3194 : rowsJ2 110 111 98 99 ≤ 13292118280398 := by decide +kernel

theorem rows22240R_3195 : rowsJ2 110 111 99 340 ≤ 1198003509068145 := by decide +kernel

theorem rows22240R_3196 : rowsJ2 111 112 0 26 ≤ 0 := by decide +kernel

theorem rows22240R_3197 : rowsJ2 111 112 26 31 ≤ 7740252224211 := by decide +kernel

theorem rows22240R_3198 : rowsJ2 111 112 31 33 ≤ 11381202172057 := by decide +kernel

theorem rows22240R_3199 : rowsJ2 111 112 33 35 ≤ 18582115123287 := by decide +kernel

theorem rows22240R_3200 : rowsJ2 111 112 35 36 ≤ 12905121953065 := by decide +kernel

theorem rows22240R_3201 : rowsJ2 111 112 36 37 ≤ 13692537015303 := by decide +kernel

theorem rows22240R_3202 : rowsJ2 111 112 37 39 ≤ 23140360138925 := by decide +kernel

theorem rows22240R_3203 : rowsJ2 111 112 39 41 ≤ 15992404286055 := by decide +kernel

theorem rows22240R_3204 : rowsJ2 111 112 41 43 ≤ 10414414031984 := by decide +kernel

theorem rows22240R_3205 : rowsJ2 111 112 43 46 ≤ 8285974340964 := by decide +kernel

theorem rows22240R_3206 : rowsJ2 111 112 46 51 ≤ 2033457230280 := by decide +kernel

theorem rows22240R_3207 : rowsJ2 111 112 51 61 ≤ 527226616142 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3193
#print axioms SieveCert.rows22240R_3207
