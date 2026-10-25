/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3316–3333 of 5796

File 292 of 465: the parts `rows22250R_3316` … `rows22250R_3333` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 92777 tests: row 109 columns 91–91, row 109 columns 92–92, row 109 columns
93–93, row 109 columns 94–94, row 109 columns 95–95, row 109 columns 96–96, row 109 columns 97–97, row 109 columns
98–98, row 109 columns 99–99, row 109 columns 100–100, row 109 columns 101–101, row 109 columns 102–102, row 109
columns 103–103, row 109 columns 104–104, row 109 columns 105–105, row 109 columns 106–106, row 109 columns 107–107,
row 109 columns 108–108), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3316 : rowsJ2 109 110 91 92 ≤ 1065188569695 := by decide +kernel

theorem rows22250R_3317 : rowsJ2 109 110 92 93 ≤ 1223629120685 := by decide +kernel

theorem rows22250R_3318 : rowsJ2 109 110 93 94 ≤ 1416853306548 := by decide +kernel

theorem rows22250R_3319 : rowsJ2 109 110 94 95 ≤ 1694517190019 := by decide +kernel

theorem rows22250R_3320 : rowsJ2 109 110 95 96 ≤ 2008851287248 := by decide +kernel

theorem rows22250R_3321 : rowsJ2 109 110 96 97 ≤ 2410565267332 := by decide +kernel

theorem rows22250R_3322 : rowsJ2 109 110 97 98 ≤ 2851172268602 := by decide +kernel

theorem rows22250R_3323 : rowsJ2 109 110 98 99 ≤ 3382496098152 := by decide +kernel

theorem rows22250R_3324 : rowsJ2 109 110 99 100 ≤ 3955305138188 := by decide +kernel

theorem rows22250R_3325 : rowsJ2 109 110 100 101 ≤ 4622602818620 := by decide +kernel

theorem rows22250R_3326 : rowsJ2 109 110 101 102 ≤ 5334386366140 := by decide +kernel

theorem rows22250R_3327 : rowsJ2 109 110 102 103 ≤ 6144909907220 := by decide +kernel

theorem rows22250R_3328 : rowsJ2 109 110 103 104 ≤ 7003374458592 := by decide +kernel

theorem rows22250R_3329 : rowsJ2 109 110 104 105 ≤ 7965362260816 := by decide +kernel

theorem rows22250R_3330 : rowsJ2 109 110 105 106 ≤ 8979254884387 := by decide +kernel

theorem rows22250R_3331 : rowsJ2 109 110 106 107 ≤ 10102047346434 := by decide +kernel

theorem rows22250R_3332 : rowsJ2 109 110 107 108 ≤ 11281280961726 := by decide +kernel

theorem rows22250R_3333 : rowsJ2 109 110 108 109 ≤ 12561180455144 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3316
#print axioms SieveCert.rows22250R_3333
