/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2166–2177 of 4715

File 180 of 351: the parts `rows22250R_2166` … `rows22250R_2177` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 87967 in units of a depth-4 test: row 89 columns 60–61, row 89 columns
62–64, row 89 columns 65–69, row 89 columns 70–74, row 89 columns 75–77, row 89 columns 78–79, row 89 columns 80–80,
row 89 columns 81–81, row 89 columns 82–82, row 89 columns 83–83, row 89 columns 84–84, row 89 columns 85–85), each
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

theorem rows22250R_2166 : rowsJ2 89 90 60 62 ≤ 0 := by decide +kernel

theorem rows22250R_2167 : rowsJ2 89 90 62 65 ≤ 0 := by decide +kernel

theorem rows22250R_2168 : rowsJ2 89 90 65 70 ≤ 0 := by decide +kernel

theorem rows22250R_2169 : rowsJ2 89 90 70 75 ≤ 0 := by decide +kernel

theorem rows22250R_2170 : rowsJ2 89 90 75 78 ≤ 383537534539 := by decide +kernel

theorem rows22250R_2171 : rowsJ2 89 90 78 80 ≤ 1308806927704 := by decide +kernel

theorem rows22250R_2172 : rowsJ2 89 90 80 81 ≤ 1188177750776 := by decide +kernel

theorem rows22250R_2173 : rowsJ2 89 90 81 82 ≤ 1645308937195 := by decide +kernel

theorem rows22250R_2174 : rowsJ2 89 90 82 83 ≤ 2236628690822 := by decide +kernel

theorem rows22250R_2175 : rowsJ2 89 90 83 84 ≤ 2989737312307 := by decide +kernel

theorem rows22250R_2176 : rowsJ2 89 90 84 85 ≤ 3898831564792 := by decide +kernel

theorem rows22250R_2177 : rowsJ2 89 90 85 86 ≤ 4990624007199 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2166
#print axioms SieveCert.rows22250R_2177
