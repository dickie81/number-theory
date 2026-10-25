/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3334–3350 of 5796

File 293 of 465: the parts `rows22250R_3334` … `rows22250R_3350` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98305 tests: row 109 columns 109–359, row 110 columns 0–19, row 110 columns
20–30, row 110 columns 31–33, row 110 columns 34–35, row 110 columns 36–36, row 110 columns 37–37, row 110 columns
38–38, row 110 columns 39–39, row 110 columns 40–40, row 110 columns 41–41, row 110 columns 42–42, row 110 columns
43–43, row 110 columns 44–44, row 110 columns 45–45, row 110 columns 46–47, row 110 columns 48–49), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3334 : rowsJ2 109 110 109 360 ≤ 13902380977080 := by decide +kernel

theorem rows22250R_3335 : rowsJ2 110 111 0 20 ≤ 0 := by decide +kernel

theorem rows22250R_3336 : rowsJ2 110 111 20 31 ≤ 785262579646 := by decide +kernel

theorem rows22250R_3337 : rowsJ2 110 111 31 34 ≤ 5558228191614 := by decide +kernel

theorem rows22250R_3338 : rowsJ2 110 111 34 36 ≤ 9408842435858 := by decide +kernel

theorem rows22250R_3339 : rowsJ2 110 111 36 37 ≤ 6938821012956 := by decide +kernel

theorem rows22250R_3340 : rowsJ2 110 111 37 38 ≤ 8816068679534 := by decide +kernel

theorem rows22250R_3341 : rowsJ2 110 111 38 39 ≤ 10610954632856 := by decide +kernel

theorem rows22250R_3342 : rowsJ2 110 111 39 40 ≤ 12501034737076 := by decide +kernel

theorem rows22250R_3343 : rowsJ2 110 111 40 41 ≤ 13937537696554 := by decide +kernel

theorem rows22250R_3344 : rowsJ2 110 111 41 42 ≤ 12225677737935 := by decide +kernel

theorem rows22250R_3345 : rowsJ2 110 111 42 43 ≤ 10674431605138 := by decide +kernel

theorem rows22250R_3346 : rowsJ2 110 111 43 44 ≤ 9279956162766 := by decide +kernel

theorem rows22250R_3347 : rowsJ2 110 111 44 45 ≤ 7954125462301 := by decide +kernel

theorem rows22250R_3348 : rowsJ2 110 111 45 46 ≤ 6696905576602 := by decide +kernel

theorem rows22250R_3349 : rowsJ2 110 111 46 48 ≤ 9897146449847 := by decide +kernel

theorem rows22250R_3350 : rowsJ2 110 111 48 50 ≤ 6033565771632 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3334
#print axioms SieveCert.rows22250R_3350
