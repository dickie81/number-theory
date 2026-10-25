/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2316–2327 of 5796

File 216 of 465: the parts `rows22250R_2316` … `rows22250R_2327` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 91850 tests: row 89 columns 41–41, row 89 columns 42–42, row 89 columns
43–43, row 89 columns 44–44, row 89 columns 45–45, row 89 columns 46–46, row 89 columns 47–47, row 89 columns 48–48,
row 89 columns 49–49, row 89 columns 50–50, row 89 columns 51–51, row 89 columns 52–52), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2316 : rowsJ2 89 90 41 42 ≤ 5085469257707 := by decide +kernel

theorem rows22250R_2317 : rowsJ2 89 90 42 43 ≤ 5994387098345 := by decide +kernel

theorem rows22250R_2318 : rowsJ2 89 90 43 44 ≤ 5217547938675 := by decide +kernel

theorem rows22250R_2319 : rowsJ2 89 90 44 45 ≤ 4194562347601 := by decide +kernel

theorem rows22250R_2320 : rowsJ2 89 90 45 46 ≤ 2334839795376 := by decide +kernel

theorem rows22250R_2321 : rowsJ2 89 90 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2322 : rowsJ2 89 90 47 48 ≤ 88975321582 := by decide +kernel

theorem rows22250R_2323 : rowsJ2 89 90 48 49 ≤ 225780003098 := by decide +kernel

theorem rows22250R_2324 : rowsJ2 89 90 49 50 ≤ 226322144605 := by decide +kernel

theorem rows22250R_2325 : rowsJ2 89 90 50 51 ≤ 181879886609 := by decide +kernel

theorem rows22250R_2326 : rowsJ2 89 90 51 52 ≤ 136483914613 := by decide +kernel

theorem rows22250R_2327 : rowsJ2 89 90 52 53 ≤ 91534532601 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2316
#print axioms SieveCert.rows22250R_2327
