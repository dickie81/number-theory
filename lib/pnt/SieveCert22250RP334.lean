/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4428–4444 of 4715

File 334 of 351: the parts `rows22250R_4428` … `rows22250R_4444` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 98033 in units of a depth-4 test: row 172 columns 45–45, row 172
columns 46–46, row 172 columns 47–47, row 172 columns 48–48, row 172 columns 49–49, row 172 columns 50–50, row 172
columns 51–51, row 172 columns 52–53, row 172 columns 54–339, row 173 columns 0–35, row 173 columns 36–37, row 173
columns 38–39, row 173 columns 40–40, row 173 columns 41–41, row 173 columns 42–42, row 173 columns 43–43, row 173
columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_4428 : rowsJ2 172 173 45 46 ≤ 21328733208875 := by decide +kernel

theorem rows22250R_4429 : rowsJ2 172 173 46 47 ≤ 23234646721517 := by decide +kernel

theorem rows22250R_4430 : rowsJ2 172 173 47 48 ≤ 20875085514562 := by decide +kernel

theorem rows22250R_4431 : rowsJ2 172 173 48 49 ≤ 18663630366128 := by decide +kernel

theorem rows22250R_4432 : rowsJ2 172 173 49 50 ≤ 16595198786308 := by decide +kernel

theorem rows22250R_4433 : rowsJ2 172 173 50 51 ≤ 14665098246366 := by decide +kernel

theorem rows22250R_4434 : rowsJ2 172 173 51 52 ≤ 12869003244094 := by decide +kernel

theorem rows22250R_4435 : rowsJ2 172 173 52 54 ≤ 20866175983797 := by decide +kernel

theorem rows22250R_4436 : rowsJ2 172 173 54 340 ≤ 2770303573502144 := by decide +kernel

theorem rows22250R_4437 : rowsJ2 173 174 0 36 ≤ 15702551844160 := by decide +kernel

theorem rows22250R_4438 : rowsJ2 173 174 36 38 ≤ 17299610088414 := by decide +kernel

theorem rows22250R_4439 : rowsJ2 173 174 38 40 ≤ 23008588031330 := by decide +kernel

theorem rows22250R_4440 : rowsJ2 173 174 40 41 ≤ 13837022869454 := by decide +kernel

theorem rows22250R_4441 : rowsJ2 173 174 41 42 ≤ 15488288554378 := by decide +kernel

theorem rows22250R_4442 : rowsJ2 173 174 42 43 ≤ 17208342061889 := by decide +kernel

theorem rows22250R_4443 : rowsJ2 173 174 43 44 ≤ 18994918989648 := by decide +kernel

theorem rows22250R_4444 : rowsJ2 173 174 44 45 ≤ 20846048153524 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4428
#print axioms SieveCert.rows22250R_4444
