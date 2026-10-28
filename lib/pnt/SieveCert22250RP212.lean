/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2603–2619 of 4715

File 212 of 351: the parts `rows22250R_2603` … `rows22250R_2619` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 96729 in units of a depth-4 test: row 99 columns 97–97, row 99 columns
98–98, row 99 columns 99–339, row 100 columns 0–17, row 100 columns 18–29, row 100 columns 30–33, row 100 columns
34–35, row 100 columns 36–36, row 100 columns 37–37, row 100 columns 38–38, row 100 columns 39–39, row 100 columns
40–40, row 100 columns 41–41, row 100 columns 42–42, row 100 columns 43–43, row 100 columns 44–44, row 100 columns
45–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2603 : rowsJ2 99 100 97 98 ≤ 5947664975759 := by decide +kernel

theorem rows22250R_2604 : rowsJ2 99 100 98 99 ≤ 6820444967259 := by decide +kernel

theorem rows22250R_2605 : rowsJ2 99 100 99 340 ≤ 7766341610138 := by decide +kernel

theorem rows22250R_2606 : rowsJ2 100 101 0 18 ≤ 0 := by decide +kernel

theorem rows22250R_2607 : rowsJ2 100 101 18 30 ≤ 425036296397 := by decide +kernel

theorem rows22250R_2608 : rowsJ2 100 101 30 34 ≤ 10973349363294 := by decide +kernel

theorem rows22250R_2609 : rowsJ2 100 101 34 36 ≤ 14386316823292 := by decide +kernel

theorem rows22250R_2610 : rowsJ2 100 101 36 37 ≤ 10277121242091 := by decide +kernel

theorem rows22250R_2611 : rowsJ2 100 101 37 38 ≤ 12274508903570 := by decide +kernel

theorem rows22250R_2612 : rowsJ2 100 101 38 39 ≤ 13830729003133 := by decide +kernel

theorem rows22250R_2613 : rowsJ2 100 101 39 40 ≤ 15504232809188 := by decide +kernel

theorem rows22250R_2614 : rowsJ2 100 101 40 41 ≤ 15263905897932 := by decide +kernel

theorem rows22250R_2615 : rowsJ2 100 101 41 42 ≤ 13359399054991 := by decide +kernel

theorem rows22250R_2616 : rowsJ2 100 101 42 43 ≤ 11585178734856 := by decide +kernel

theorem rows22250R_2617 : rowsJ2 100 101 43 44 ≤ 9998723417196 := by decide +kernel

theorem rows22250R_2618 : rowsJ2 100 101 44 45 ≤ 8494324862233 := by decide +kernel

theorem rows22250R_2619 : rowsJ2 100 101 45 47 ≤ 12803986165954 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2603
#print axioms SieveCert.rows22250R_2619
