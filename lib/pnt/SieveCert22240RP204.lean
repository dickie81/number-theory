/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2356–2370 of 5066

File 204 of 387: the parts `rows22240R_2356` … `rows22240R_2370` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96120 in units of a depth-4 test: row 91 columns 42–42, row 91 columns
43–43, row 91 columns 44–44, row 91 columns 45–45, row 91 columns 46–46, row 91 columns 47–47, row 91 columns 48–48,
row 91 columns 49–49, row 91 columns 50–50, row 91 columns 51–51, row 91 columns 52–52, row 91 columns 53–53, row 91
columns 54–54, row 91 columns 55–55, row 91 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2356 : rowsJ2 91 92 42 43 ≤ 12248973644633 := by decide +kernel

theorem rows22240R_2357 : rowsJ2 91 92 43 44 ≤ 13743135746751 := by decide +kernel

theorem rows22240R_2358 : rowsJ2 91 92 44 45 ≤ 15115729323298 := by decide +kernel

theorem rows22240R_2359 : rowsJ2 91 92 45 46 ≤ 16366047478664 := by decide +kernel

theorem rows22240R_2360 : rowsJ2 91 92 46 47 ≤ 15958508191781 := by decide +kernel

theorem rows22240R_2361 : rowsJ2 91 92 47 48 ≤ 14175348611590 := by decide +kernel

theorem rows22240R_2362 : rowsJ2 91 92 48 49 ≤ 12508265502981 := by decide +kernel

theorem rows22240R_2363 : rowsJ2 91 92 49 50 ≤ 8312222324668 := by decide +kernel

theorem rows22240R_2364 : rowsJ2 91 92 50 51 ≤ 5069407926895 := by decide +kernel

theorem rows22240R_2365 : rowsJ2 91 92 51 52 ≤ 2157854141438 := by decide +kernel

theorem rows22240R_2366 : rowsJ2 91 92 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2367 : rowsJ2 91 92 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2368 : rowsJ2 91 92 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2369 : rowsJ2 91 92 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2370 : rowsJ2 91 92 56 57 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2356
#print axioms SieveCert.rows22240R_2370
