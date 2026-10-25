/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2462–2473 of 5796

File 227 of 465: the parts `rows22250R_2462` … `rows22250R_2473` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 98631 tests: row 92 columns 43–43, row 92 columns 44–44, row 92 columns
45–45, row 92 columns 46–46, row 92 columns 47–47, row 92 columns 48–48, row 92 columns 49–49, row 92 columns 50–50,
row 92 columns 51–51, row 92 columns 52–52, row 92 columns 53–53, row 92 columns 54–54), each a sum of refined costs
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

theorem rows22250R_2462 : rowsJ2 92 93 43 44 ≤ 8149851570504 := by decide +kernel

theorem rows22250R_2463 : rowsJ2 92 93 44 45 ≤ 9369451885678 := by decide +kernel

theorem rows22250R_2464 : rowsJ2 92 93 45 46 ≤ 10596533249362 := by decide +kernel

theorem rows22250R_2465 : rowsJ2 92 93 46 47 ≤ 9216817864143 := by decide +kernel

theorem rows22250R_2466 : rowsJ2 92 93 47 48 ≤ 6697518594328 := by decide +kernel

theorem rows22250R_2467 : rowsJ2 92 93 48 49 ≤ 3779674847502 := by decide +kernel

theorem rows22250R_2468 : rowsJ2 92 93 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2469 : rowsJ2 92 93 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2470 : rowsJ2 92 93 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2471 : rowsJ2 92 93 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2472 : rowsJ2 92 93 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2473 : rowsJ2 92 93 54 55 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2462
#print axioms SieveCert.rows22250R_2473
