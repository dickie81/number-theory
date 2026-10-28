/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2421–2430 of 5066

File 209 of 387: the parts `rows22240R_2421` … `rows22240R_2430` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 88139 in units of a depth-4 test: row 92 columns 74–77, row 92 columns
78–79, row 92 columns 80–80, row 92 columns 81–81, row 92 columns 82–82, row 92 columns 83–83, row 92 columns 84–84,
row 92 columns 85–85, row 92 columns 86–86, row 92 columns 87–87), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2421 : rowsJ2 92 93 74 78 ≤ 249272974443 := by decide +kernel

theorem rows22240R_2422 : rowsJ2 92 93 78 80 ≤ 1037158574904 := by decide +kernel

theorem rows22240R_2423 : rowsJ2 92 93 80 81 ≤ 986627770453 := by decide +kernel

theorem rows22240R_2424 : rowsJ2 92 93 81 82 ≤ 1455918654313 := by decide +kernel

theorem rows22240R_2425 : rowsJ2 92 93 82 83 ≤ 2081907615393 := by decide +kernel

theorem rows22240R_2426 : rowsJ2 92 93 83 84 ≤ 2858045550604 := by decide +kernel

theorem rows22240R_2427 : rowsJ2 92 93 84 85 ≤ 3812243059681 := by decide +kernel

theorem rows22240R_2428 : rowsJ2 92 93 85 86 ≤ 4941077733637 := by decide +kernel

theorem rows22240R_2429 : rowsJ2 92 93 86 87 ≤ 6177548562010 := by decide +kernel

theorem rows22240R_2430 : rowsJ2 92 93 87 88 ≤ 7213309581574 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2421
#print axioms SieveCert.rows22240R_2430
