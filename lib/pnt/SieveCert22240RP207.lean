/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2391–2405 of 5066

File 207 of 387: the parts `rows22240R_2391` … `rows22240R_2405` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98719 in units of a depth-4 test: row 92 columns 0–16, row 92 columns
17–19, row 92 columns 20–23, row 92 columns 24–29, row 92 columns 30–34, row 92 columns 35–36, row 92 columns 37–38,
row 92 columns 39–39, row 92 columns 40–40, row 92 columns 41–41, row 92 columns 42–42, row 92 columns 43–43, row 92
columns 44–44, row 92 columns 45–45, row 92 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2391 : rowsJ2 92 93 0 17 ≤ 0 := by decide +kernel

theorem rows22240R_2392 : rowsJ2 92 93 17 20 ≤ 0 := by decide +kernel

theorem rows22240R_2393 : rowsJ2 92 93 20 24 ≤ 0 := by decide +kernel

theorem rows22240R_2394 : rowsJ2 92 93 24 30 ≤ 0 := by decide +kernel

theorem rows22240R_2395 : rowsJ2 92 93 30 35 ≤ 4481434775283 := by decide +kernel

theorem rows22240R_2396 : rowsJ2 92 93 35 37 ≤ 7960923983099 := by decide +kernel

theorem rows22240R_2397 : rowsJ2 92 93 37 39 ≤ 13889395188062 := by decide +kernel

theorem rows22240R_2398 : rowsJ2 92 93 39 40 ≤ 8767339934335 := by decide +kernel

theorem rows22240R_2399 : rowsJ2 92 93 40 41 ≤ 10011973441068 := by decide +kernel

theorem rows22240R_2400 : rowsJ2 92 93 41 42 ≤ 11372103466040 := by decide +kernel

theorem rows22240R_2401 : rowsJ2 92 93 42 43 ≤ 12842058096154 := by decide +kernel

theorem rows22240R_2402 : rowsJ2 92 93 43 44 ≤ 14360386528476 := by decide +kernel

theorem rows22240R_2403 : rowsJ2 92 93 44 45 ≤ 15755907678567 := by decide +kernel

theorem rows22240R_2404 : rowsJ2 92 93 45 46 ≤ 16870532766302 := by decide +kernel

theorem rows22240R_2405 : rowsJ2 92 93 46 47 ≤ 15070037665618 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2391
#print axioms SieveCert.rows22240R_2405
