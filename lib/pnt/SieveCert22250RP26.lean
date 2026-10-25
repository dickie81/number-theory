/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 313–324 of 5796

File 26 of 465: the parts `rows22250R_313` … `rows22250R_324` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94421 tests: row 40 columns 40–359, row 41 columns 0–13, row 41 columns
14–16, row 41 columns 17–18, row 41 columns 19–20, row 41 columns 21–22, row 41 columns 23–24, row 41 columns 25–26,
row 41 columns 27–27, row 41 columns 28–28, row 41 columns 29–29, row 41 columns 30–30), each a sum of refined costs
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

theorem rows22250R_313 : rowsJ2 40 41 40 360 ≤ 374765152192 := by decide +kernel

theorem rows22250R_314 : rowsJ2 41 42 0 14 ≤ 603973354957 := by decide +kernel

theorem rows22250R_315 : rowsJ2 41 42 14 17 ≤ 1651729917052 := by decide +kernel

theorem rows22250R_316 : rowsJ2 41 42 17 19 ≤ 1534381905425 := by decide +kernel

theorem rows22250R_317 : rowsJ2 41 42 19 21 ≤ 1650664829050 := by decide +kernel

theorem rows22250R_318 : rowsJ2 41 42 21 23 ≤ 1574188840692 := by decide +kernel

theorem rows22250R_319 : rowsJ2 41 42 23 25 ≤ 1397448883689 := by decide +kernel

theorem rows22250R_320 : rowsJ2 41 42 25 27 ≤ 1174540080949 := by decide +kernel

theorem rows22250R_321 : rowsJ2 41 42 27 28 ≤ 509146888737 := by decide +kernel

theorem rows22250R_322 : rowsJ2 41 42 28 29 ≤ 464039936978 := by decide +kernel

theorem rows22250R_323 : rowsJ2 41 42 29 30 ≤ 429337802273 := by decide +kernel

theorem rows22250R_324 : rowsJ2 41 42 30 31 ≤ 402730925248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_313
#print axioms SieveCert.rows22250R_324
