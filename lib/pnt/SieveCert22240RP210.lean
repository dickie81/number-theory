/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2431–2439 of 5066

File 210 of 387: the parts `rows22240R_2431` … `rows22240R_2439` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 94093 in units of a depth-4 test: row 92 columns 88–88, row 92 columns
89–89, row 92 columns 90–90, row 92 columns 91–91, row 92 columns 92–339, row 93 columns 0–15, row 93 columns 16–19,
row 93 columns 20–24, row 93 columns 25–31), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_2431 : rowsJ2 92 93 88 89 ≤ 6384347183741 := by decide +kernel

theorem rows22240R_2432 : rowsJ2 92 93 89 90 ≤ 5652178324269 := by decide +kernel

theorem rows22240R_2433 : rowsJ2 92 93 90 91 ≤ 5075256148019 := by decide +kernel

theorem rows22240R_2434 : rowsJ2 92 93 91 92 ≤ 4643658302278 := by decide +kernel

theorem rows22240R_2435 : rowsJ2 92 93 92 340 ≤ 4678681871581 := by decide +kernel

theorem rows22240R_2436 : rowsJ2 93 94 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2437 : rowsJ2 93 94 16 20 ≤ 0 := by decide +kernel

theorem rows22240R_2438 : rowsJ2 93 94 20 25 ≤ 0 := by decide +kernel

theorem rows22240R_2439 : rowsJ2 93 94 25 32 ≤ 201100923594 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2431
#print axioms SieveCert.rows22240R_2439
