/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2479–2494 of 4715

File 204 of 351: the parts `rows22250R_2479` … `rows22250R_2494` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 97922 in units of a depth-4 test: row 97 columns 17–26, row 97 columns
27–32, row 97 columns 33–35, row 97 columns 36–37, row 97 columns 38–38, row 97 columns 39–39, row 97 columns 40–40,
row 97 columns 41–41, row 97 columns 42–42, row 97 columns 43–43, row 97 columns 44–44, row 97 columns 45–45, row 97
columns 46–46, row 97 columns 47–47, row 97 columns 48–49, row 97 columns 50–51), each a sum of refined costs
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

theorem rows22250R_2479 : rowsJ2 97 98 17 27 ≤ 0 := by decide +kernel

theorem rows22250R_2480 : rowsJ2 97 98 27 33 ≤ 4176896493826 := by decide +kernel

theorem rows22250R_2481 : rowsJ2 97 98 33 36 ≤ 14825186490430 := by decide +kernel

theorem rows22250R_2482 : rowsJ2 97 98 36 38 ≤ 18982598317376 := by decide +kernel

theorem rows22250R_2483 : rowsJ2 97 98 38 39 ≤ 12120535672031 := by decide +kernel

theorem rows22250R_2484 : rowsJ2 97 98 39 40 ≤ 13630730724437 := by decide +kernel

theorem rows22250R_2485 : rowsJ2 97 98 40 41 ≤ 15148783840987 := by decide +kernel

theorem rows22250R_2486 : rowsJ2 97 98 41 42 ≤ 16535771000974 := by decide +kernel

theorem rows22250R_2487 : rowsJ2 97 98 42 43 ≤ 14687207311628 := by decide +kernel

theorem rows22250R_2488 : rowsJ2 97 98 43 44 ≤ 12963773611158 := by decide +kernel

theorem rows22250R_2489 : rowsJ2 97 98 44 45 ≤ 11321661682048 := by decide +kernel

theorem rows22250R_2490 : rowsJ2 97 98 45 46 ≤ 9697790110873 := by decide +kernel

theorem rows22250R_2491 : rowsJ2 97 98 46 47 ≤ 8153396131043 := by decide +kernel

theorem rows22250R_2492 : rowsJ2 97 98 47 48 ≤ 6688498147636 := by decide +kernel

theorem rows22250R_2493 : rowsJ2 97 98 48 50 ≤ 9699358959241 := by decide +kernel

theorem rows22250R_2494 : rowsJ2 97 98 50 52 ≤ 5960302479177 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2479
#print axioms SieveCert.rows22250R_2494
