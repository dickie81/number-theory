/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 628–636 of 5066

File 64 of 387: the parts `rows22240R_628` … `rows22240R_636` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 92913 in units of a depth-4 test: row 52 columns 37–37, row 52 columns
38–38, row 52 columns 39–39, row 52 columns 40–40, row 52 columns 41–41, row 52 columns 42–42, row 52 columns 43–43,
row 52 columns 44–44, row 52 columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_628 : rowsJ2 52 53 37 38 ≤ 7990523507 := by decide +kernel

theorem rows22240R_629 : rowsJ2 52 53 38 39 ≤ 3989939342 := by decide +kernel

theorem rows22240R_630 : rowsJ2 52 53 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_631 : rowsJ2 52 53 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_632 : rowsJ2 52 53 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_633 : rowsJ2 52 53 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_634 : rowsJ2 52 53 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_635 : rowsJ2 52 53 44 45 ≤ 75637338369 := by decide +kernel

theorem rows22240R_636 : rowsJ2 52 53 45 46 ≤ 221197017760 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_628
#print axioms SieveCert.rows22240R_636
