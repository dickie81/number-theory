/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 562–568 of 5066

File 57 of 387: the parts `rows22240R_562` … `rows22240R_568` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 94513 in units of a depth-4 test: row 50 columns 34–34, row 50 columns
35–35, row 50 columns 36–36, row 50 columns 37–37, row 50 columns 38–38, row 50 columns 39–39, row 50 columns
40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_562 : rowsJ2 50 51 34 35 ≤ 79683974138 := by decide +kernel

theorem rows22240R_563 : rowsJ2 50 51 35 36 ≤ 59293028904 := by decide +kernel

theorem rows22240R_564 : rowsJ2 50 51 36 37 ≤ 45163559623 := by decide +kernel

theorem rows22240R_565 : rowsJ2 50 51 37 38 ≤ 29830672379 := by decide +kernel

theorem rows22240R_566 : rowsJ2 50 51 38 39 ≤ 20779400311 := by decide +kernel

theorem rows22240R_567 : rowsJ2 50 51 39 40 ≤ 10474043552 := by decide +kernel

theorem rows22240R_568 : rowsJ2 50 51 40 41 ≤ 6493036826 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_562
#print axioms SieveCert.rows22240R_568
