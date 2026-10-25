/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2560–2571 of 5796

File 235 of 465: the parts `rows22250R_2560` … `rows22250R_2571` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 95082 tests: row 94 columns 45–45, row 94 columns 46–46, row 94 columns
47–47, row 94 columns 48–48, row 94 columns 49–49, row 94 columns 50–50, row 94 columns 51–51, row 94 columns 52–52,
row 94 columns 53–53, row 94 columns 54–54, row 94 columns 55–55, row 94 columns 56–56), each a sum of refined costs
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

theorem rows22250R_2560 : rowsJ2 94 95 45 46 ≤ 11665989676708 := by decide +kernel

theorem rows22250R_2561 : rowsJ2 94 95 46 47 ≤ 12779298417640 := by decide +kernel

theorem rows22250R_2562 : rowsJ2 94 95 47 48 ≤ 13749645203098 := by decide +kernel

theorem rows22250R_2563 : rowsJ2 94 95 48 49 ≤ 11413498948185 := by decide +kernel

theorem rows22250R_2564 : rowsJ2 94 95 49 50 ≤ 7000634797421 := by decide +kernel

theorem rows22250R_2565 : rowsJ2 94 95 50 51 ≤ 3333492459917 := by decide +kernel

theorem rows22250R_2566 : rowsJ2 94 95 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2567 : rowsJ2 94 95 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2568 : rowsJ2 94 95 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2569 : rowsJ2 94 95 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2570 : rowsJ2 94 95 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2571 : rowsJ2 94 95 56 57 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2560
#print axioms SieveCert.rows22250R_2571
