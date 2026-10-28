/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2523–2539 of 4715

File 207 of 351: the parts `rows22250R_2523` … `rows22250R_2539` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 98424 in units of a depth-4 test: row 98 columns 33–34, row 98 columns
35–36, row 98 columns 37–37, row 98 columns 38–38, row 98 columns 39–39, row 98 columns 40–40, row 98 columns 41–41,
row 98 columns 42–42, row 98 columns 43–43, row 98 columns 44–44, row 98 columns 45–45, row 98 columns 46–46, row 98
columns 47–48, row 98 columns 49–50, row 98 columns 51–52, row 98 columns 53–55, row 98 columns 56–60), each a sum
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

theorem rows22250R_2523 : rowsJ2 98 99 33 35 ≤ 9185060519139 := by decide +kernel

theorem rows22250R_2524 : rowsJ2 98 99 35 37 ≤ 16022749879518 := by decide +kernel

theorem rows22250R_2525 : rowsJ2 98 99 37 38 ≤ 11208742284270 := by decide +kernel

theorem rows22250R_2526 : rowsJ2 98 99 38 39 ≤ 12690130213261 := by decide +kernel

theorem rows22250R_2527 : rowsJ2 98 99 39 40 ≤ 14182320321314 := by decide +kernel

theorem rows22250R_2528 : rowsJ2 98 99 40 41 ≤ 15727378445101 := by decide +kernel

theorem rows22250R_2529 : rowsJ2 98 99 41 42 ≤ 15487115046146 := by decide +kernel

theorem rows22250R_2530 : rowsJ2 98 99 42 43 ≤ 13642812650926 := by decide +kernel

theorem rows22250R_2531 : rowsJ2 98 99 43 44 ≤ 11985374705541 := by decide +kernel

theorem rows22250R_2532 : rowsJ2 98 99 44 45 ≤ 10346835814200 := by decide +kernel

theorem rows22250R_2533 : rowsJ2 98 99 45 46 ≤ 8788646208456 := by decide +kernel

theorem rows22250R_2534 : rowsJ2 98 99 46 47 ≤ 7310778582241 := by decide +kernel

theorem rows22250R_2535 : rowsJ2 98 99 47 49 ≤ 10610967483562 := by decide +kernel

theorem rows22250R_2536 : rowsJ2 98 99 49 51 ≤ 6459232986088 := by decide +kernel

theorem rows22250R_2537 : rowsJ2 98 99 51 53 ≤ 3613923022279 := by decide +kernel

theorem rows22250R_2538 : rowsJ2 98 99 53 56 ≤ 1691306409010 := by decide +kernel

theorem rows22250R_2539 : rowsJ2 98 99 56 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2523
#print axioms SieveCert.rows22250R_2539
