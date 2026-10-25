/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3127–3142 of 5796

File 280 of 465: the parts `rows22250R_3127` … `rows22250R_3142` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98611 tests: row 105 columns 98–98, row 105 columns 99–99, row 105 columns
100–100, row 105 columns 101–101, row 105 columns 102–102, row 105 columns 103–103, row 105 columns 104–104, row 105
columns 105–359, row 106 columns 0–16, row 106 columns 17–28, row 106 columns 29–33, row 106 columns 34–35, row 106
columns 36–37, row 106 columns 38–38, row 106 columns 39–39, row 106 columns 40–40), each a sum of refined costs
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

theorem rows22250R_3127 : rowsJ2 105 106 98 99 ≤ 3032734390023 := by decide +kernel

theorem rows22250R_3128 : rowsJ2 105 106 99 100 ≤ 3447593397776 := by decide +kernel

theorem rows22250R_3129 : rowsJ2 105 106 100 101 ≤ 3950157061887 := by decide +kernel

theorem rows22250R_3130 : rowsJ2 105 106 101 102 ≤ 4491442906151 := by decide +kernel

theorem rows22250R_3131 : rowsJ2 105 106 102 103 ≤ 5123980756854 := by decide +kernel

theorem rows22250R_3132 : rowsJ2 105 106 103 104 ≤ 5798015572758 := by decide +kernel

theorem rows22250R_3133 : rowsJ2 105 106 104 105 ≤ 6567291221392 := by decide +kernel

theorem rows22250R_3134 : rowsJ2 105 106 105 360 ≤ 7381253971188 := by decide +kernel

theorem rows22250R_3135 : rowsJ2 106 107 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_3136 : rowsJ2 106 107 17 29 ≤ 0 := by decide +kernel

theorem rows22250R_3137 : rowsJ2 106 107 29 34 ≤ 3811177006708 := by decide +kernel

theorem rows22250R_3138 : rowsJ2 106 107 34 36 ≤ 6686992757839 := by decide +kernel

theorem rows22250R_3139 : rowsJ2 106 107 36 38 ≤ 11824089126826 := by decide +kernel

theorem rows22250R_3140 : rowsJ2 106 107 38 39 ≤ 8342572594307 := by decide +kernel

theorem rows22250R_3141 : rowsJ2 106 107 39 40 ≤ 10363291953624 := by decide +kernel

theorem rows22250R_3142 : rowsJ2 106 107 40 41 ≤ 11680933949259 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3127
#print axioms SieveCert.rows22250R_3142
