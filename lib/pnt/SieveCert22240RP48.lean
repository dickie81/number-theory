/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 483–490 of 5066

File 48 of 387: the parts `rows22240R_483` … `rows22240R_490` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 97894 in units of a depth-4 test: row 47 columns 40–40, row 47 columns
41–41, row 47 columns 42–42, row 47 columns 43–43, row 47 columns 44–44, row 47 columns 45–45, row 47 columns 46–46,
row 47 columns 47–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_483 : rowsJ2 47 48 40 41 ≤ 38700454988 := by decide +kernel

theorem rows22240R_484 : rowsJ2 47 48 41 42 ≤ 27758251907 := by decide +kernel

theorem rows22240R_485 : rowsJ2 47 48 42 43 ≤ 16867624320 := by decide +kernel

theorem rows22240R_486 : rowsJ2 47 48 43 44 ≤ 11630105845 := by decide +kernel

theorem rows22240R_487 : rowsJ2 47 48 44 45 ≤ 86086482895 := by decide +kernel

theorem rows22240R_488 : rowsJ2 47 48 45 46 ≤ 238141429835 := by decide +kernel

theorem rows22240R_489 : rowsJ2 47 48 46 47 ≤ 458265573509 := by decide +kernel

theorem rows22240R_490 : rowsJ2 47 48 47 340 ≤ 972751049154 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_483
#print axioms SieveCert.rows22240R_490
