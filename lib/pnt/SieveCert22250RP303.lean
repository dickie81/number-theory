/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3499–3515 of 5796

File 303 of 465: the parts `rows22250R_3499` … `rows22250R_3515` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 96723 tests: row 113 columns 96–97, row 113 columns 98–98, row 113 columns
99–99, row 113 columns 100–100, row 113 columns 101–101, row 113 columns 102–102, row 113 columns 103–103, row 113
columns 104–104, row 113 columns 105–105, row 113 columns 106–106, row 113 columns 107–359, row 114 columns 0–25,
row 114 columns 26–31, row 114 columns 32–33, row 114 columns 34–35, row 114 columns 36–36, row 114 columns 37–37),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3499 : rowsJ2 113 114 96 98 ≤ 6548865325019 := by decide +kernel

theorem rows22250R_3500 : rowsJ2 113 114 98 99 ≤ 4276916532375 := by decide +kernel

theorem rows22250R_3501 : rowsJ2 113 114 99 100 ≤ 5025582261495 := by decide +kernel

theorem rows22250R_3502 : rowsJ2 113 114 100 101 ≤ 5863567336377 := by decide +kernel

theorem rows22250R_3503 : rowsJ2 113 114 101 102 ≤ 6752693040170 := by decide +kernel

theorem rows22250R_3504 : rowsJ2 113 114 102 103 ≤ 7735807903585 := by decide +kernel

theorem rows22250R_3505 : rowsJ2 113 114 103 104 ≤ 8774057320138 := by decide +kernel

theorem rows22250R_3506 : rowsJ2 113 114 104 105 ≤ 9911572913735 := by decide +kernel

theorem rows22250R_3507 : rowsJ2 113 114 105 106 ≤ 11108811294204 := by decide +kernel

theorem rows22250R_3508 : rowsJ2 113 114 106 107 ≤ 12411278039563 := by decide +kernel

theorem rows22250R_3509 : rowsJ2 113 114 107 360 ≤ 630156557864931 := by decide +kernel

theorem rows22250R_3510 : rowsJ2 114 115 0 26 ≤ 0 := by decide +kernel

theorem rows22250R_3511 : rowsJ2 114 115 26 32 ≤ 3550836541205 := by decide +kernel

theorem rows22250R_3512 : rowsJ2 114 115 32 34 ≤ 7211759477071 := by decide +kernel

theorem rows22250R_3513 : rowsJ2 114 115 34 36 ≤ 12885259765731 := by decide +kernel

theorem rows22250R_3514 : rowsJ2 114 115 36 37 ≤ 8946800892637 := by decide +kernel

theorem rows22250R_3515 : rowsJ2 114 115 37 38 ≤ 10692878448081 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3499
#print axioms SieveCert.rows22250R_3515
