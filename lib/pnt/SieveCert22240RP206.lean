/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2384–2390 of 5066

File 206 of 387: the parts `rows22240R_2384` … `rows22240R_2390` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 97455 in units of a depth-4 test: row 91 columns 85–85, row 91 columns
86–86, row 91 columns 87–87, row 91 columns 88–88, row 91 columns 89–89, row 91 columns 90–90, row 91 columns
91–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22240R_2384 : rowsJ2 91 92 85 86 ≤ 4931889077514 := by decide +kernel

theorem rows22240R_2385 : rowsJ2 91 92 86 87 ≤ 6252840732557 := by decide +kernel

theorem rows22240R_2386 : rowsJ2 91 92 87 88 ≤ 7475515981404 := by decide +kernel

theorem rows22240R_2387 : rowsJ2 91 92 88 89 ≤ 7576534040337 := by decide +kernel

theorem rows22240R_2388 : rowsJ2 91 92 89 90 ≤ 6731110118987 := by decide +kernel

theorem rows22240R_2389 : rowsJ2 91 92 90 91 ≤ 6034039371415 := by decide +kernel

theorem rows22240R_2390 : rowsJ2 91 92 91 340 ≤ 5474572587254 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2384
#print axioms SieveCert.rows22240R_2390
