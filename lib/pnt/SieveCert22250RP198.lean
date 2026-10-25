/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2396–2411 of 4715

File 198 of 351: the parts `rows22250R_2396` … `rows22250R_2411` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96066 tests: row 95 columns 25–32, row 95 columns 33–35, row 95 columns
36–37, row 95 columns 38–38, row 95 columns 39–39, row 95 columns 40–40, row 95 columns 41–41, row 95 columns 42–42,
row 95 columns 43–43, row 95 columns 44–44, row 95 columns 45–45, row 95 columns 46–46, row 95 columns 47–47, row 95
columns 48–48, row 95 columns 49–49, row 95 columns 50–51), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2396 : rowsJ2 95 96 25 33 ≤ 3260407423576 := by decide +kernel

theorem rows22250R_2397 : rowsJ2 95 96 33 36 ≤ 12316979014889 := by decide +kernel

theorem rows22250R_2398 : rowsJ2 95 96 36 38 ≤ 16399938644848 := by decide +kernel

theorem rows22250R_2399 : rowsJ2 95 96 38 39 ≤ 10768429366932 := by decide +kernel

theorem rows22250R_2400 : rowsJ2 95 96 39 40 ≤ 12317590079444 := by decide +kernel

theorem rows22250R_2401 : rowsJ2 95 96 40 41 ≤ 13874312758956 := by decide +kernel

theorem rows22250R_2402 : rowsJ2 95 96 41 42 ≤ 15376596166412 := by decide +kernel

theorem rows22250R_2403 : rowsJ2 95 96 42 43 ≤ 16646384443031 := by decide +kernel

theorem rows22250R_2404 : rowsJ2 95 96 43 44 ≤ 14854671681117 := by decide +kernel

theorem rows22250R_2405 : rowsJ2 95 96 44 45 ≤ 13144385153130 := by decide +kernel

theorem rows22250R_2406 : rowsJ2 95 96 45 46 ≤ 11453674636676 := by decide +kernel

theorem rows22250R_2407 : rowsJ2 95 96 46 47 ≤ 9842432942635 := by decide +kernel

theorem rows22250R_2408 : rowsJ2 95 96 47 48 ≤ 8248146630120 := by decide +kernel

theorem rows22250R_2409 : rowsJ2 95 96 48 49 ≤ 6831078001086 := by decide +kernel

theorem rows22250R_2410 : rowsJ2 95 96 49 50 ≤ 5587691108638 := by decide +kernel

theorem rows22250R_2411 : rowsJ2 95 96 50 52 ≤ 8124642382242 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2396
#print axioms SieveCert.rows22250R_2411
