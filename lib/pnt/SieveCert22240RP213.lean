/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2472–2479 of 5066

File 213 of 387: the parts `rows22240R_2472` … `rows22240R_2479` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 96118 in units of a depth-4 test: row 93 columns 84–84, row 93 columns
85–85, row 93 columns 86–86, row 93 columns 87–87, row 93 columns 88–88, row 93 columns 89–89, row 93 columns 90–90,
row 93 columns 91–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2472 : rowsJ2 93 94 84 85 ≤ 3813292402936 := by decide +kernel

theorem rows22240R_2473 : rowsJ2 93 94 85 86 ≤ 4953184554094 := by decide +kernel

theorem rows22240R_2474 : rowsJ2 93 94 86 87 ≤ 6004395801825 := by decide +kernel

theorem rows22240R_2475 : rowsJ2 93 94 87 88 ≤ 6045266545206 := by decide +kernel

theorem rows22240R_2476 : rowsJ2 93 94 88 89 ≤ 5294658864979 := by decide +kernel

theorem rows22240R_2477 : rowsJ2 93 94 89 90 ≤ 4682430274999 := by decide +kernel

theorem rows22240R_2478 : rowsJ2 93 94 90 91 ≤ 4233009451681 := by decide +kernel

theorem rows22240R_2479 : rowsJ2 93 94 91 92 ≤ 4233026438781 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2472
#print axioms SieveCert.rows22240R_2479
