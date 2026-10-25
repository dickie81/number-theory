/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2219–2230 of 5796

File 209 of 465: the parts `rows22250R_2219` … `rows22250R_2230` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 97262 tests: row 87 columns 42–42, row 87 columns 43–43, row 87 columns
44–44, row 87 columns 45–45, row 87 columns 46–46, row 87 columns 47–47, row 87 columns 48–48, row 87 columns 49–49,
row 87 columns 50–50, row 87 columns 51–51, row 87 columns 52–52, row 87 columns 53–53), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2219 : rowsJ2 87 88 42 43 ≤ 2890578076633 := by decide +kernel

theorem rows22250R_2220 : rowsJ2 87 88 43 44 ≤ 1619667829351 := by decide +kernel

theorem rows22250R_2221 : rowsJ2 87 88 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_2222 : rowsJ2 87 88 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_2223 : rowsJ2 87 88 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2224 : rowsJ2 87 88 47 48 ≤ 90276142326 := by decide +kernel

theorem rows22250R_2225 : rowsJ2 87 88 48 49 ≤ 361732936427 := by decide +kernel

theorem rows22250R_2226 : rowsJ2 87 88 49 50 ≤ 497844348761 := by decide +kernel

theorem rows22250R_2227 : rowsJ2 87 88 50 51 ≤ 454237310211 := by decide +kernel

theorem rows22250R_2228 : rowsJ2 87 88 51 52 ≤ 363554063088 := by decide +kernel

theorem rows22250R_2229 : rowsJ2 87 88 52 53 ≤ 273786177893 := by decide +kernel

theorem rows22250R_2230 : rowsJ2 87 88 53 54 ≤ 182013616413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2219
#print axioms SieveCert.rows22250R_2230
