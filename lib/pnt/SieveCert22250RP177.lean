/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2127–2138 of 4715

File 177 of 351: the parts `rows22250R_2127` … `rows22250R_2138` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 94717 in units of a depth-4 test: row 88 columns 63–65, row 88 columns
66–69, row 88 columns 70–74, row 88 columns 75–77, row 88 columns 78–79, row 88 columns 80–80, row 88 columns 81–81,
row 88 columns 82–82, row 88 columns 83–83, row 88 columns 84–84, row 88 columns 85–85, row 88 columns 86–86), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_2127 : rowsJ2 88 89 63 66 ≤ 0 := by decide +kernel

theorem rows22250R_2128 : rowsJ2 88 89 66 70 ≤ 0 := by decide +kernel

theorem rows22250R_2129 : rowsJ2 88 89 70 75 ≤ 0 := by decide +kernel

theorem rows22250R_2130 : rowsJ2 88 89 75 78 ≤ 386377876967 := by decide +kernel

theorem rows22250R_2131 : rowsJ2 88 89 78 80 ≤ 1318499485829 := by decide +kernel

theorem rows22250R_2132 : rowsJ2 88 89 80 81 ≤ 1196976972161 := by decide +kernel

theorem rows22250R_2133 : rowsJ2 88 89 81 82 ≤ 1657442856444 := by decide +kernel

theorem rows22250R_2134 : rowsJ2 88 89 82 83 ≤ 2251720465070 := by decide +kernel

theorem rows22250R_2135 : rowsJ2 88 89 83 84 ≤ 3005746293500 := by decide +kernel

theorem rows22250R_2136 : rowsJ2 88 89 84 85 ≤ 3910328443503 := by decide +kernel

theorem rows22250R_2137 : rowsJ2 88 89 85 86 ≤ 4997179443248 := by decide +kernel

theorem rows22250R_2138 : rowsJ2 88 89 86 87 ≤ 6260300540593 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2127
#print axioms SieveCert.rows22250R_2138
