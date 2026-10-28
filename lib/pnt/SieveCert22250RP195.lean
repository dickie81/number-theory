/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2355–2371 of 4715

File 195 of 351: the parts `rows22250R_2355` … `rows22250R_2371` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 96798 in units of a depth-4 test: row 94 columns 35–36, row 94 columns
37–37, row 94 columns 38–38, row 94 columns 39–39, row 94 columns 40–40, row 94 columns 41–41, row 94 columns 42–42,
row 94 columns 43–43, row 94 columns 44–44, row 94 columns 45–45, row 94 columns 46–46, row 94 columns 47–47, row 94
columns 48–48, row 94 columns 49–49, row 94 columns 50–50, row 94 columns 51–52, row 94 columns 53–54), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2355 : rowsJ2 94 95 35 37 ≤ 11857491140678 := by decide +kernel

theorem rows22250R_2356 : rowsJ2 94 95 37 38 ≤ 8540304510850 := by decide +kernel

theorem rows22250R_2357 : rowsJ2 94 95 38 39 ≤ 9988243173628 := by decide +kernel

theorem rows22250R_2358 : rowsJ2 94 95 39 40 ≤ 11558344390407 := by decide +kernel

theorem rows22250R_2359 : rowsJ2 94 95 40 41 ≤ 13135832402673 := by decide +kernel

theorem rows22250R_2360 : rowsJ2 94 95 41 42 ≤ 14718096537986 := by decide +kernel

theorem rows22250R_2361 : rowsJ2 94 95 42 43 ≤ 16068113222427 := by decide +kernel

theorem rows22250R_2362 : rowsJ2 94 95 43 44 ≤ 15769240180964 := by decide +kernel

theorem rows22250R_2363 : rowsJ2 94 95 44 45 ≤ 13995577036463 := by decide +kernel

theorem rows22250R_2364 : rowsJ2 94 95 45 46 ≤ 12302358123641 := by decide +kernel

theorem rows22250R_2365 : rowsJ2 94 95 46 47 ≤ 10628014490951 := by decide +kernel

theorem rows22250R_2366 : rowsJ2 94 95 47 48 ≤ 9032248952735 := by decide +kernel

theorem rows22250R_2367 : rowsJ2 94 95 48 49 ≤ 7551761652966 := by decide +kernel

theorem rows22250R_2368 : rowsJ2 94 95 49 50 ≤ 6243558494338 := by decide +kernel

theorem rows22250R_2369 : rowsJ2 94 95 50 51 ≤ 5104390335511 := by decide +kernel

theorem rows22250R_2370 : rowsJ2 94 95 51 53 ≤ 4913197296187 := by decide +kernel

theorem rows22250R_2371 : rowsJ2 94 95 53 55 ≤ 676947227754 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2355
#print axioms SieveCert.rows22250R_2371
