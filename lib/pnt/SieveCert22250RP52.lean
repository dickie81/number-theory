/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 529–537 of 4715

File 52 of 351: the parts `rows22250R_529` … `rows22250R_537` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 95806 in units of a depth-4 test: row 50 columns 26–26, row 50 columns
27–27, row 50 columns 28–28, row 50 columns 29–29, row 50 columns 30–30, row 50 columns 31–31, row 50 columns 32–32,
row 50 columns 33–33, row 50 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_529 : rowsJ2 50 51 26 27 ≤ 137062077698 := by decide +kernel

theorem rows22250R_530 : rowsJ2 50 51 27 28 ≤ 120375046476 := by decide +kernel

theorem rows22250R_531 : rowsJ2 50 51 28 29 ≤ 105969392156 := by decide +kernel

theorem rows22250R_532 : rowsJ2 50 51 29 30 ≤ 88932588551 := by decide +kernel

theorem rows22250R_533 : rowsJ2 50 51 30 31 ≤ 69611730086 := by decide +kernel

theorem rows22250R_534 : rowsJ2 50 51 31 32 ≤ 52586941075 := by decide +kernel

theorem rows22250R_535 : rowsJ2 50 51 32 33 ≤ 36925002379 := by decide +kernel

theorem rows22250R_536 : rowsJ2 50 51 33 34 ≤ 24228790831 := by decide +kernel

theorem rows22250R_537 : rowsJ2 50 51 34 35 ≤ 14198584500 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_529
#print axioms SieveCert.rows22250R_537
