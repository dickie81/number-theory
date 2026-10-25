/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3083–3097 of 5796

File 277 of 465: the parts `rows22250R_3083` … `rows22250R_3097` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95087 tests: row 104 columns 103–103, row 104 columns 104–359, row 105
columns 0–16, row 105 columns 17–26, row 105 columns 27–33, row 105 columns 34–35, row 105 columns 36–37, row 105
columns 38–38, row 105 columns 39–39, row 105 columns 40–40, row 105 columns 41–41, row 105 columns 42–42, row 105
columns 43–43, row 105 columns 44–44, row 105 columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_3083 : rowsJ2 104 105 103 104 ≤ 5610957067335 := by decide +kernel

theorem rows22250R_3084 : rowsJ2 104 105 104 360 ≤ 6316405904410 := by decide +kernel

theorem rows22250R_3085 : rowsJ2 105 106 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_3086 : rowsJ2 105 106 17 27 ≤ 0 := by decide +kernel

theorem rows22250R_3087 : rowsJ2 105 106 27 34 ≤ 3308224423832 := by decide +kernel

theorem rows22250R_3088 : rowsJ2 105 106 34 36 ≤ 6118803420099 := by decide +kernel

theorem rows22250R_3089 : rowsJ2 105 106 36 38 ≤ 11112027783103 := by decide +kernel

theorem rows22250R_3090 : rowsJ2 105 106 38 39 ≤ 7780397803729 := by decide +kernel

theorem rows22250R_3091 : rowsJ2 105 106 39 40 ≤ 9722375858155 := by decide +kernel

theorem rows22250R_3092 : rowsJ2 105 106 40 41 ≤ 11056412593529 := by decide +kernel

theorem rows22250R_3093 : rowsJ2 105 106 41 42 ≤ 12396345024379 := by decide +kernel

theorem rows22250R_3094 : rowsJ2 105 106 42 43 ≤ 13691335197794 := by decide +kernel

theorem rows22250R_3095 : rowsJ2 105 106 43 44 ≤ 13494449809569 := by decide +kernel

theorem rows22250R_3096 : rowsJ2 105 106 44 45 ≤ 11950509084301 := by decide +kernel

theorem rows22250R_3097 : rowsJ2 105 106 45 46 ≤ 10473260738815 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3083
#print axioms SieveCert.rows22250R_3097
