/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2554–2570 of 4715

File 209 of 351: the parts `rows22250R_2554` … `rows22250R_2570` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 96956 in units of a depth-4 test: row 98 columns 90–90, row 98 columns
91–91, row 98 columns 92–92, row 98 columns 93–93, row 98 columns 94–94, row 98 columns 95–95, row 98 columns 96–96,
row 98 columns 97–97, row 98 columns 98–339, row 99 columns 0–17, row 99 columns 18–29, row 99 columns 30–33, row 99
columns 34–35, row 99 columns 36–36, row 99 columns 37–37, row 99 columns 38–38, row 99 columns 39–39), each a sum
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

theorem rows22250R_2554 : rowsJ2 98 99 90 91 ≤ 2263725524478 := by decide +kernel

theorem rows22250R_2555 : rowsJ2 98 99 91 92 ≤ 2544038332371 := by decide +kernel

theorem rows22250R_2556 : rowsJ2 98 99 92 93 ≤ 2864935245730 := by decide +kernel

theorem rows22250R_2557 : rowsJ2 98 99 93 94 ≤ 3291209943104 := by decide +kernel

theorem rows22250R_2558 : rowsJ2 98 99 94 95 ≤ 3762012147945 := by decide +kernel

theorem rows22250R_2559 : rowsJ2 98 99 95 96 ≤ 4342275408824 := by decide +kernel

theorem rows22250R_2560 : rowsJ2 98 99 96 97 ≤ 4970156048800 := by decide +kernel

theorem rows22250R_2561 : rowsJ2 98 99 97 98 ≤ 5712131818897 := by decide +kernel

theorem rows22250R_2562 : rowsJ2 98 99 98 340 ≤ 6505327467118 := by decide +kernel

theorem rows22250R_2563 : rowsJ2 99 100 0 18 ≤ 0 := by decide +kernel

theorem rows22250R_2564 : rowsJ2 99 100 18 30 ≤ 427946863055 := by decide +kernel

theorem rows22250R_2565 : rowsJ2 99 100 30 34 ≤ 9612490216104 := by decide +kernel

theorem rows22250R_2566 : rowsJ2 99 100 34 36 ≤ 13257934782706 := by decide +kernel

theorem rows22250R_2567 : rowsJ2 99 100 36 37 ≤ 9674556695477 := by decide +kernel

theorem rows22250R_2568 : rowsJ2 99 100 37 38 ≤ 11796919140226 := by decide +kernel

theorem rows22250R_2569 : rowsJ2 99 100 38 39 ≤ 13260343036174 := by decide +kernel

theorem rows22250R_2570 : rowsJ2 99 100 39 40 ≤ 14842191234006 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2554
#print axioms SieveCert.rows22250R_2570
