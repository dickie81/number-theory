/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2044–2057 of 4715

File 171 of 351: the parts `rows22250R_2044` … `rows22250R_2057` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 99060 in units of a depth-4 test: row 86 columns 59–60, row 86 columns
61–62, row 86 columns 63–64, row 86 columns 65–67, row 86 columns 68–71, row 86 columns 72–75, row 86 columns 76–78,
row 86 columns 79–79, row 86 columns 80–80, row 86 columns 81–81, row 86 columns 82–82, row 86 columns 83–83, row 86
columns 84–84, row 86 columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2044 : rowsJ2 86 87 59 61 ≤ 0 := by decide +kernel

theorem rows22250R_2045 : rowsJ2 86 87 61 63 ≤ 0 := by decide +kernel

theorem rows22250R_2046 : rowsJ2 86 87 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_2047 : rowsJ2 86 87 65 68 ≤ 0 := by decide +kernel

theorem rows22250R_2048 : rowsJ2 86 87 68 72 ≤ 0 := by decide +kernel

theorem rows22250R_2049 : rowsJ2 86 87 72 76 ≤ 17174870640 := by decide +kernel

theorem rows22250R_2050 : rowsJ2 86 87 76 79 ≤ 884110446190 := by decide +kernel

theorem rows22250R_2051 : rowsJ2 86 87 79 80 ≤ 829223104454 := by decide +kernel

theorem rows22250R_2052 : rowsJ2 86 87 80 81 ≤ 1214972276370 := by decide +kernel

theorem rows22250R_2053 : rowsJ2 86 87 81 82 ≤ 1683685192539 := by decide +kernel

theorem rows22250R_2054 : rowsJ2 86 87 82 83 ≤ 2281705090803 := by decide +kernel

theorem rows22250R_2055 : rowsJ2 86 87 83 84 ≤ 3037207337043 := by decide +kernel

theorem rows22250R_2056 : rowsJ2 86 87 84 85 ≤ 3939776680240 := by decide +kernel

theorem rows22250R_2057 : rowsJ2 86 87 85 86 ≤ 5016181573267 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2044
#print axioms SieveCert.rows22250R_2057
