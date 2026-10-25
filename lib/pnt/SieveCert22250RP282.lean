/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3159–3172 of 5796

File 282 of 465: the parts `rows22250R_3159` … `rows22250R_3172` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96092 tests: row 106 columns 76–79, row 106 columns 80–82, row 106 columns
83–83, row 106 columns 84–84, row 106 columns 85–85, row 106 columns 86–86, row 106 columns 87–87, row 106 columns
88–88, row 106 columns 89–89, row 106 columns 90–90, row 106 columns 91–91, row 106 columns 92–92, row 106 columns
93–93, row 106 columns 94–94), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3159 : rowsJ2 106 107 76 80 ≤ 0 := by decide +kernel

theorem rows22250R_3160 : rowsJ2 106 107 80 83 ≤ 503402976121 := by decide +kernel

theorem rows22250R_3161 : rowsJ2 106 107 83 84 ≤ 512152418373 := by decide +kernel

theorem rows22250R_3162 : rowsJ2 106 107 84 85 ≤ 777207419517 := by decide +kernel

theorem rows22250R_3163 : rowsJ2 106 107 85 86 ≤ 1087011888870 := by decide +kernel

theorem rows22250R_3164 : rowsJ2 106 107 86 87 ≤ 1455674682585 := by decide +kernel

theorem rows22250R_3165 : rowsJ2 106 107 87 88 ≤ 1870838565112 := by decide +kernel

theorem rows22250R_3166 : rowsJ2 106 107 88 89 ≤ 1741205613896 := by decide +kernel

theorem rows22250R_3167 : rowsJ2 106 107 89 90 ≤ 1609103052635 := by decide +kernel

theorem rows22250R_3168 : rowsJ2 106 107 90 91 ≤ 1519293516217 := by decide +kernel

theorem rows22250R_3169 : rowsJ2 106 107 91 92 ≤ 1491803500775 := by decide +kernel

theorem rows22250R_3170 : rowsJ2 106 107 92 93 ≤ 1542300391864 := by decide +kernel

theorem rows22250R_3171 : rowsJ2 106 107 93 94 ≤ 1658200401549 := by decide +kernel

theorem rows22250R_3172 : rowsJ2 106 107 94 95 ≤ 1819113158099 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3159
#print axioms SieveCert.rows22250R_3172
