/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2370–2380 of 5796

File 220 of 465: the parts `rows22250R_2370` … `rows22250R_2380` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98606 tests: row 90 columns 47–47, row 90 columns 48–48, row 90 columns
49–49, row 90 columns 50–50, row 90 columns 51–51, row 90 columns 52–52, row 90 columns 53–53, row 90 columns 54–54,
row 90 columns 55–55, row 90 columns 56–56, row 90 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2370 : rowsJ2 90 91 47 48 ≤ 44628092886 := by decide +kernel

theorem rows22250R_2371 : rowsJ2 90 91 48 49 ≤ 135345850573 := by decide +kernel

theorem rows22250R_2372 : rowsJ2 90 91 49 50 ≤ 90727294717 := by decide +kernel

theorem rows22250R_2373 : rowsJ2 90 91 50 51 ≤ 90760682155 := by decide +kernel

theorem rows22250R_2374 : rowsJ2 90 91 51 52 ≤ 45647358710 := by decide +kernel

theorem rows22250R_2375 : rowsJ2 90 91 52 53 ≤ 45680822434 := by decide +kernel

theorem rows22250R_2376 : rowsJ2 90 91 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2377 : rowsJ2 90 91 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2378 : rowsJ2 90 91 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2379 : rowsJ2 90 91 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2380 : rowsJ2 90 91 57 58 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2370
#print axioms SieveCert.rows22250R_2380
