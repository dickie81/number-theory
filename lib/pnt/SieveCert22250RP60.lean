/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 562–569 of 5796

File 60 of 465: the parts `rows22250R_562` … `rows22250R_569` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 97988 tests: row 50 columns 41–41, row 50 columns 42–42, row 50 columns
43–43, row 50 columns 44–44, row 50 columns 45–45, row 50 columns 46–46, row 50 columns 47–47, row 50 columns
48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_562 : rowsJ2 50 51 41 42 ≤ 4884879798 := by decide +kernel

theorem rows22250R_563 : rowsJ2 50 51 42 43 ≤ 3977425847 := by decide +kernel

theorem rows22250R_564 : rowsJ2 50 51 43 44 ≤ 2031292653 := by decide +kernel

theorem rows22250R_565 : rowsJ2 50 51 44 45 ≤ 2036690637 := by decide +kernel

theorem rows22250R_566 : rowsJ2 50 51 45 46 ≤ 1532224614 := by decide +kernel

theorem rows22250R_567 : rowsJ2 50 51 46 47 ≤ 1537060622 := by decide +kernel

theorem rows22250R_568 : rowsJ2 50 51 47 48 ≤ 124773989514 := by decide +kernel

theorem rows22250R_569 : rowsJ2 50 51 48 49 ≤ 555640260613 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_562
#print axioms SieveCert.rows22250R_569
