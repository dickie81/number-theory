/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2096–2111 of 5796

File 200 of 465: the parts `rows22250R_2096` … `rows22250R_2111` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96610 tests: row 84 columns 63–63, row 84 columns 64–64, row 84 columns
65–65, row 84 columns 66–66, row 84 columns 67–67, row 84 columns 68–68, row 84 columns 69–69, row 84 columns 70–70,
row 84 columns 71–71, row 84 columns 72–73, row 84 columns 74–75, row 84 columns 76–77, row 84 columns 78–79, row 84
columns 80–81, row 84 columns 82–83, row 84 columns 84–359), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2096 : rowsJ2 84 85 63 64 ≤ 238533088980 := by decide +kernel

theorem rows22250R_2097 : rowsJ2 84 85 64 65 ≤ 191453094313 := by decide +kernel

theorem rows22250R_2098 : rowsJ2 84 85 65 66 ≤ 95940632444 := by decide +kernel

theorem rows22250R_2099 : rowsJ2 84 85 66 67 ≤ 47819386549 := by decide +kernel

theorem rows22250R_2100 : rowsJ2 84 85 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_2101 : rowsJ2 84 85 68 69 ≤ 0 := by decide +kernel

theorem rows22250R_2102 : rowsJ2 84 85 69 70 ≤ 0 := by decide +kernel

theorem rows22250R_2103 : rowsJ2 84 85 70 71 ≤ 0 := by decide +kernel

theorem rows22250R_2104 : rowsJ2 84 85 71 72 ≤ 0 := by decide +kernel

theorem rows22250R_2105 : rowsJ2 84 85 72 74 ≤ 0 := by decide +kernel

theorem rows22250R_2106 : rowsJ2 84 85 74 76 ≤ 0 := by decide +kernel

theorem rows22250R_2107 : rowsJ2 84 85 76 78 ≤ 0 := by decide +kernel

theorem rows22250R_2108 : rowsJ2 84 85 78 80 ≤ 0 := by decide +kernel

theorem rows22250R_2109 : rowsJ2 84 85 80 82 ≤ 229307469139 := by decide +kernel

theorem rows22250R_2110 : rowsJ2 84 85 82 84 ≤ 1482152193200 := by decide +kernel

theorem rows22250R_2111 : rowsJ2 84 85 84 360 ≤ 1617305441545 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2096
#print axioms SieveCert.rows22250R_2111
