/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2112–2126 of 5796

File 201 of 465: the parts `rows22250R_2112` … `rows22250R_2126` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96322 tests: row 85 columns 0–17, row 85 columns 18–19, row 85 columns
20–21, row 85 columns 22–23, row 85 columns 24–25, row 85 columns 26–27, row 85 columns 28–29, row 85 columns 30–32,
row 85 columns 33–36, row 85 columns 37–39, row 85 columns 40–41, row 85 columns 42–42, row 85 columns 43–43, row 85
columns 44–44, row 85 columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2112 : rowsJ2 85 86 0 18 ≤ 62481578954 := by decide +kernel

theorem rows22250R_2113 : rowsJ2 85 86 18 20 ≤ 7968076809 := by decide +kernel

theorem rows22250R_2114 : rowsJ2 85 86 20 22 ≤ 7181634896 := by decide +kernel

theorem rows22250R_2115 : rowsJ2 85 86 22 24 ≤ 2136709411 := by decide +kernel

theorem rows22250R_2116 : rowsJ2 85 86 24 26 ≤ 0 := by decide +kernel

theorem rows22250R_2117 : rowsJ2 85 86 26 28 ≤ 0 := by decide +kernel

theorem rows22250R_2118 : rowsJ2 85 86 28 30 ≤ 0 := by decide +kernel

theorem rows22250R_2119 : rowsJ2 85 86 30 33 ≤ 0 := by decide +kernel

theorem rows22250R_2120 : rowsJ2 85 86 33 37 ≤ 301698355773 := by decide +kernel

theorem rows22250R_2121 : rowsJ2 85 86 37 40 ≤ 3839150050128 := by decide +kernel

theorem rows22250R_2122 : rowsJ2 85 86 40 42 ≤ 2626252823712 := by decide +kernel

theorem rows22250R_2123 : rowsJ2 85 86 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_2124 : rowsJ2 85 86 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_2125 : rowsJ2 85 86 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_2126 : rowsJ2 85 86 45 46 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2112
#print axioms SieveCert.rows22250R_2126
