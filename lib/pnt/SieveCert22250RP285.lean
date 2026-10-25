/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3205–3218 of 5796

File 285 of 465: the parts `rows22250R_3205` … `rows22250R_3218` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 95025 tests: row 107 columns 58–62, row 107 columns 63–70, row 107 columns
71–75, row 107 columns 76–79, row 107 columns 80–81, row 107 columns 82–83, row 107 columns 84–84, row 107 columns
85–85, row 107 columns 86–86, row 107 columns 87–87, row 107 columns 88–88, row 107 columns 89–89, row 107 columns
90–90, row 107 columns 91–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3205 : rowsJ2 107 108 58 63 ≤ 0 := by decide +kernel

theorem rows22250R_3206 : rowsJ2 107 108 63 71 ≤ 0 := by decide +kernel

theorem rows22250R_3207 : rowsJ2 107 108 71 76 ≤ 0 := by decide +kernel

theorem rows22250R_3208 : rowsJ2 107 108 76 80 ≤ 0 := by decide +kernel

theorem rows22250R_3209 : rowsJ2 107 108 80 82 ≤ 195671537626 := by decide +kernel

theorem rows22250R_3210 : rowsJ2 107 108 82 84 ≤ 813445173902 := by decide +kernel

theorem rows22250R_3211 : rowsJ2 107 108 84 85 ≤ 771293181440 := by decide +kernel

theorem rows22250R_3212 : rowsJ2 107 108 85 86 ≤ 1079312640936 := by decide +kernel

theorem rows22250R_3213 : rowsJ2 107 108 86 87 ≤ 1444828961464 := by decide +kernel

theorem rows22250R_3214 : rowsJ2 107 108 87 88 ≤ 1580624384282 := by decide +kernel

theorem rows22250R_3215 : rowsJ2 107 108 88 89 ≤ 1461129836830 := by decide +kernel

theorem rows22250R_3216 : rowsJ2 107 108 89 90 ≤ 1339225155103 := by decide +kernel

theorem rows22250R_3217 : rowsJ2 107 108 90 91 ≤ 1292787349862 := by decide +kernel

theorem rows22250R_3218 : rowsJ2 107 108 91 92 ≤ 1311471469287 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3205
#print axioms SieveCert.rows22250R_3218
