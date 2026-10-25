/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3578–3593 of 5796

File 308 of 465: the parts `rows22250R_3578` … `rows22250R_3593` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95645 tests: row 115 columns 102–102, row 115 columns 103–103, row 115
columns 104–104, row 115 columns 105–105, row 115 columns 106–359, row 116 columns 0–26, row 116 columns 27–31, row
116 columns 32–33, row 116 columns 34–35, row 116 columns 36–36, row 116 columns 37–37, row 116 columns 38–38, row
116 columns 39–39, row 116 columns 40–41, row 116 columns 42–43, row 116 columns 44–45), each a sum of refined costs
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

theorem rows22250R_3578 : rowsJ2 115 116 102 103 ≤ 8640711019417 := by decide +kernel

theorem rows22250R_3579 : rowsJ2 115 116 103 104 ≤ 9764146713830 := by decide +kernel

theorem rows22250R_3580 : rowsJ2 115 116 104 105 ≤ 10992046784758 := by decide +kernel

theorem rows22250R_3581 : rowsJ2 115 116 105 106 ≤ 12284060497371 := by decide +kernel

theorem rows22250R_3582 : rowsJ2 115 116 106 360 ≤ 896179736952323 := by decide +kernel

theorem rows22250R_3583 : rowsJ2 116 117 0 27 ≤ 0 := by decide +kernel

theorem rows22250R_3584 : rowsJ2 116 117 27 32 ≤ 5255361474138 := by decide +kernel

theorem rows22250R_3585 : rowsJ2 116 117 32 34 ≤ 8513610432755 := by decide +kernel

theorem rows22250R_3586 : rowsJ2 116 117 34 36 ≤ 14685962026267 := by decide +kernel

theorem rows22250R_3587 : rowsJ2 116 117 36 37 ≤ 9769746995825 := by decide +kernel

theorem rows22250R_3588 : rowsJ2 116 117 37 38 ≤ 11777719155784 := by decide +kernel

theorem rows22250R_3589 : rowsJ2 116 117 38 39 ≤ 10762120287122 := by decide +kernel

theorem rows22250R_3590 : rowsJ2 116 117 39 40 ≤ 9816227547798 := by decide +kernel

theorem rows22250R_3591 : rowsJ2 116 117 40 42 ≤ 15193078750451 := by decide +kernel

theorem rows22250R_3592 : rowsJ2 116 117 42 44 ≤ 10398912235139 := by decide +kernel

theorem rows22250R_3593 : rowsJ2 116 117 44 46 ≤ 6562276291401 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3578
#print axioms SieveCert.rows22250R_3593
