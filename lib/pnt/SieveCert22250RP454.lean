/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5616–5631 of 5796

File 454 of 465: the parts `rows22250R_5616` … `rows22250R_5631` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96591 tests: row 192 columns 37–38, row 192 columns 39–39, row 192 columns
40–40, row 192 columns 41–41, row 192 columns 42–42, row 192 columns 43–43, row 192 columns 44–44, row 192 columns
45–45, row 192 columns 46–46, row 192 columns 47–47, row 192 columns 48–359, row 193 columns 0–34, row 193 columns
35–36, row 193 columns 37–38, row 193 columns 39–39, row 193 columns 40–40), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5616 : rowsJ2 192 193 37 39 ≤ 25263281755347 := by decide +kernel

theorem rows22250R_5617 : rowsJ2 192 193 39 40 ≤ 16780587016310 := by decide +kernel

theorem rows22250R_5618 : rowsJ2 192 193 40 41 ≤ 18522236004535 := by decide +kernel

theorem rows22250R_5619 : rowsJ2 192 193 41 42 ≤ 20326782361625 := by decide +kernel

theorem rows22250R_5620 : rowsJ2 192 193 42 43 ≤ 22192586349521 := by decide +kernel

theorem rows22250R_5621 : rowsJ2 192 193 43 44 ≤ 24118272035155 := by decide +kernel

theorem rows22250R_5622 : rowsJ2 192 193 44 45 ≤ 26102718266649 := by decide +kernel

theorem rows22250R_5623 : rowsJ2 192 193 45 46 ≤ 23609440985267 := by decide +kernel

theorem rows22250R_5624 : rowsJ2 192 193 46 47 ≤ 21265952634283 := by decide +kernel

theorem rows22250R_5625 : rowsJ2 192 193 47 48 ≤ 19066841477672 := by decide +kernel

theorem rows22250R_5626 : rowsJ2 192 193 48 360 ≤ 3164835444767352 := by decide +kernel

theorem rows22250R_5627 : rowsJ2 193 194 0 35 ≤ 16165066775740 := by decide +kernel

theorem rows22250R_5628 : rowsJ2 193 194 35 37 ≤ 17663682293541 := by decide +kernel

theorem rows22250R_5629 : rowsJ2 193 194 37 39 ≤ 27364823693621 := by decide +kernel

theorem rows22250R_5630 : rowsJ2 193 194 39 40 ≤ 18013518281941 := by decide +kernel

theorem rows22250R_5631 : rowsJ2 193 194 40 41 ≤ 19824746489769 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5616
#print axioms SieveCert.rows22250R_5631
