/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2701–2714 of 5796

File 247 of 465: the parts `rows22250R_2701` … `rows22250R_2714` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98519 tests: row 97 columns 41–41, row 97 columns 42–42, row 97 columns
43–43, row 97 columns 44–44, row 97 columns 45–45, row 97 columns 46–46, row 97 columns 47–47, row 97 columns 48–48,
row 97 columns 49–49, row 97 columns 50–50, row 97 columns 51–51, row 97 columns 52–52, row 97 columns 53–53, row 97
columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2701 : rowsJ2 97 98 41 42 ≤ 8397713392427 := by decide +kernel

theorem rows22250R_2702 : rowsJ2 97 98 42 43 ≤ 9524156690833 := by decide +kernel

theorem rows22250R_2703 : rowsJ2 97 98 43 44 ≤ 10662620994916 := by decide +kernel

theorem rows22250R_2704 : rowsJ2 97 98 44 45 ≤ 11889313338144 := by decide +kernel

theorem rows22250R_2705 : rowsJ2 97 98 45 46 ≤ 13108801504046 := by decide +kernel

theorem rows22250R_2706 : rowsJ2 97 98 46 47 ≤ 14181928523846 := by decide +kernel

theorem rows22250R_2707 : rowsJ2 97 98 47 48 ≤ 13893613764084 := by decide +kernel

theorem rows22250R_2708 : rowsJ2 97 98 48 49 ≤ 12380736618597 := by decide +kernel

theorem rows22250R_2709 : rowsJ2 97 98 49 50 ≤ 11008778805272 := by decide +kernel

theorem rows22250R_2710 : rowsJ2 97 98 50 51 ≤ 9726875989316 := by decide +kernel

theorem rows22250R_2711 : rowsJ2 97 98 51 52 ≤ 6470241435768 := by decide +kernel

theorem rows22250R_2712 : rowsJ2 97 98 52 53 ≤ 3934989590988 := by decide +kernel

theorem rows22250R_2713 : rowsJ2 97 98 53 54 ≤ 1663180417415 := by decide +kernel

theorem rows22250R_2714 : rowsJ2 97 98 54 55 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2701
#print axioms SieveCert.rows22250R_2714
