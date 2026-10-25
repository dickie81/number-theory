/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3219–3235 of 5796

File 286 of 465: the parts `rows22250R_3219` … `rows22250R_3235` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97458 tests: row 107 columns 92–92, row 107 columns 93–93, row 107 columns
94–94, row 107 columns 95–95, row 107 columns 96–96, row 107 columns 97–97, row 107 columns 98–98, row 107 columns
99–99, row 107 columns 100–100, row 107 columns 101–101, row 107 columns 102–102, row 107 columns 103–103, row 107
columns 104–104, row 107 columns 105–105, row 107 columns 106–106, row 107 columns 107–359, row 108 columns 0–17),
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

theorem rows22250R_3219 : rowsJ2 107 108 92 93 ≤ 1408786755438 := by decide +kernel

theorem rows22250R_3220 : rowsJ2 107 108 93 94 ≤ 1538043894681 := by decide +kernel

theorem rows22250R_3221 : rowsJ2 107 108 94 95 ≤ 1748113366877 := by decide +kernel

theorem rows22250R_3222 : rowsJ2 107 108 95 96 ≤ 1992682483153 := by decide +kernel

theorem rows22250R_3223 : rowsJ2 107 108 96 97 ≤ 2321715550365 := by decide +kernel

theorem rows22250R_3224 : rowsJ2 107 108 97 98 ≤ 2687223983187 := by decide +kernel

theorem rows22250R_3225 : rowsJ2 107 108 98 99 ≤ 3140240937124 := by decide +kernel

theorem rows22250R_3226 : rowsJ2 107 108 99 100 ≤ 3632046559523 := by decide +kernel

theorem rows22250R_3227 : rowsJ2 107 108 100 101 ≤ 4214804164771 := by decide +kernel

theorem rows22250R_3228 : rowsJ2 107 108 101 102 ≤ 4839035408203 := by decide +kernel

theorem rows22250R_3229 : rowsJ2 107 108 102 103 ≤ 5558100090173 := by decide +kernel

theorem rows22250R_3230 : rowsJ2 107 108 103 104 ≤ 6321735134873 := by decide +kernel

theorem rows22250R_3231 : rowsJ2 107 108 104 105 ≤ 7184568820040 := by decide +kernel

theorem rows22250R_3232 : rowsJ2 107 108 105 106 ≤ 8095528461456 := by decide +kernel

theorem rows22250R_3233 : rowsJ2 107 108 106 107 ≤ 9110589238410 := by decide +kernel

theorem rows22250R_3234 : rowsJ2 107 108 107 360 ≤ 10177845828464 := by decide +kernel

theorem rows22250R_3235 : rowsJ2 108 109 0 18 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3219
#print axioms SieveCert.rows22250R_3235
