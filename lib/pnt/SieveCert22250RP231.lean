/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2512–2523 of 5796

File 231 of 465: the parts `rows22250R_2512` … `rows22250R_2523` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 97980 tests: row 93 columns 45–45, row 93 columns 46–46, row 93 columns
47–47, row 93 columns 48–48, row 93 columns 49–49, row 93 columns 50–50, row 93 columns 51–51, row 93 columns 52–52,
row 93 columns 53–53, row 93 columns 54–54, row 93 columns 55–55, row 93 columns 56–56), each a sum of refined costs
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

theorem rows22250R_2512 : rowsJ2 93 94 45 46 ≤ 11131470331417 := by decide +kernel

theorem rows22250R_2513 : rowsJ2 93 94 46 47 ≤ 12304561280938 := by decide +kernel

theorem rows22250R_2514 : rowsJ2 93 94 47 48 ≤ 10073389417606 := by decide +kernel

theorem rows22250R_2515 : rowsJ2 93 94 48 49 ≤ 7446310351205 := by decide +kernel

theorem rows22250R_2516 : rowsJ2 93 94 49 50 ≤ 3655723976805 := by decide +kernel

theorem rows22250R_2517 : rowsJ2 93 94 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2518 : rowsJ2 93 94 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2519 : rowsJ2 93 94 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2520 : rowsJ2 93 94 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2521 : rowsJ2 93 94 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2522 : rowsJ2 93 94 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2523 : rowsJ2 93 94 56 57 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2512
#print axioms SieveCert.rows22250R_2523
