/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4908–4924 of 5066

File 378 of 387: the parts `rows22240R_4908` … `rows22240R_4924` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96348 in units of a depth-4 test: row 182 columns 36–37, row 182
columns 38–38, row 182 columns 39–39, row 182 columns 40–40, row 182 columns 41–41, row 182 columns 42–42, row 182
columns 43–43, row 182 columns 44–44, row 182 columns 45–45, row 182 columns 46–339, row 183 columns 0–33, row 183
columns 34–35, row 183 columns 36–37, row 183 columns 38–38, row 183 columns 39–39, row 183 columns 40–40, row 183
columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4908 : rowsJ2 182 183 36 38 ≤ 34008504749266 := by decide +kernel

theorem rows22240R_4909 : rowsJ2 182 183 38 39 ≤ 20762662038360 := by decide +kernel

theorem rows22240R_4910 : rowsJ2 182 183 39 40 ≤ 22906039071243 := by decide +kernel

theorem rows22240R_4911 : rowsJ2 182 183 40 41 ≤ 25126223140289 := by decide +kernel

theorem rows22240R_4912 : rowsJ2 182 183 41 42 ≤ 27421419955745 := by decide +kernel

theorem rows22240R_4913 : rowsJ2 182 183 42 43 ≤ 29790193986960 := by decide +kernel

theorem rows22240R_4914 : rowsJ2 182 183 43 44 ≤ 26809598230666 := by decide +kernel

theorem rows22240R_4915 : rowsJ2 182 183 44 45 ≤ 24017369954752 := by decide +kernel

theorem rows22240R_4916 : rowsJ2 182 183 45 46 ≤ 21406275321648 := by decide +kernel

theorem rows22240R_4917 : rowsJ2 182 183 46 340 ≤ 3401525122037314 := by decide +kernel

theorem rows22240R_4918 : rowsJ2 183 184 0 34 ≤ 23292095247386 := by decide +kernel

theorem rows22240R_4919 : rowsJ2 183 184 34 36 ≤ 24083126764087 := by decide +kernel

theorem rows22240R_4920 : rowsJ2 183 184 36 38 ≤ 36801330129920 := by decide +kernel

theorem rows22240R_4921 : rowsJ2 183 184 38 39 ≤ 22310721264366 := by decide +kernel

theorem rows22240R_4922 : rowsJ2 183 184 39 40 ≤ 24542227314028 := by decide +kernel

theorem rows22240R_4923 : rowsJ2 183 184 40 41 ≤ 26851261958487 := by decide +kernel

theorem rows22240R_4924 : rowsJ2 183 184 41 42 ≤ 29236210326192 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4908
#print axioms SieveCert.rows22240R_4924
