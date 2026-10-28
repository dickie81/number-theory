/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3066–3080 of 5066

File 253 of 387: the parts `rows22240R_3066` … `rows22240R_3080` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95063 in units of a depth-4 test: row 107 columns 31–33, row 107
columns 34–35, row 107 columns 36–36, row 107 columns 37–37, row 107 columns 38–38, row 107 columns 39–39, row 107
columns 40–40, row 107 columns 41–42, row 107 columns 43–44, row 107 columns 45–46, row 107 columns 47–49, row 107
columns 50–54, row 107 columns 55–63, row 107 columns 64–70, row 107 columns 71–74), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3066 : rowsJ2 107 108 31 34 ≤ 14516385375642 := by decide +kernel

theorem rows22240R_3067 : rowsJ2 107 108 34 36 ≤ 18536918309673 := by decide +kernel

theorem rows22240R_3068 : rowsJ2 107 108 36 37 ≤ 12323185290579 := by decide +kernel

theorem rows22240R_3069 : rowsJ2 107 108 37 38 ≤ 14947547038071 := by decide +kernel

theorem rows22240R_3070 : rowsJ2 107 108 38 39 ≤ 14770942024812 := by decide +kernel

theorem rows22240R_3071 : rowsJ2 107 108 39 40 ≤ 12673155135478 := by decide +kernel

theorem rows22240R_3072 : rowsJ2 107 108 40 41 ≤ 10782870668572 := by decide +kernel

theorem rows22240R_3073 : rowsJ2 107 108 41 43 ≤ 16698947799352 := by decide +kernel

theorem rows22240R_3074 : rowsJ2 107 108 43 45 ≤ 11401843480557 := by decide +kernel

theorem rows22240R_3075 : rowsJ2 107 108 45 47 ≤ 6901789707523 := by decide +kernel

theorem rows22240R_3076 : rowsJ2 107 108 47 50 ≤ 3866097512478 := by decide +kernel

theorem rows22240R_3077 : rowsJ2 107 108 50 55 ≤ 378569197466 := by decide +kernel

theorem rows22240R_3078 : rowsJ2 107 108 55 64 ≤ 433574306463 := by decide +kernel

theorem rows22240R_3079 : rowsJ2 107 108 64 71 ≤ 0 := by decide +kernel

theorem rows22240R_3080 : rowsJ2 107 108 71 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3066
#print axioms SieveCert.rows22240R_3080
