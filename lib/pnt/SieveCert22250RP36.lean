/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 378–384 of 4715

File 36 of 351: the parts `rows22250R_378` … `rows22250R_384` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97988 tests: row 44 columns 36–36, row 44 columns 37–37, row 44 columns
38–38, row 44 columns 39–39, row 44 columns 40–40, row 44 columns 41–41, row 44 columns 42–42), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_378 : rowsJ2 44 45 36 37 ≤ 115897647465 := by decide +kernel

theorem rows22250R_379 : rowsJ2 44 45 37 38 ≤ 91045114031 := by decide +kernel

theorem rows22250R_380 : rowsJ2 44 45 38 39 ≤ 70484498660 := by decide +kernel

theorem rows22250R_381 : rowsJ2 44 45 39 40 ≤ 51930497806 := by decide +kernel

theorem rows22250R_382 : rowsJ2 44 45 40 41 ≤ 37622570487 := by decide +kernel

theorem rows22250R_383 : rowsJ2 44 45 41 42 ≤ 26176429901 := by decide +kernel

theorem rows22250R_384 : rowsJ2 44 45 42 43 ≤ 18943919235 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_378
#print axioms SieveCert.rows22250R_384
