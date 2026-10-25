/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4320–4334 of 5796

File 358 of 465: the parts `rows22250R_4320` … `rows22250R_4334` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97609 tests: row 139 columns 73–73, row 139 columns 74–74, row 139 columns
75–75, row 139 columns 76–76, row 139 columns 77–77, row 139 columns 78–78, row 139 columns 79–79, row 139 columns
80–80, row 139 columns 81–82, row 139 columns 83–84, row 139 columns 85–87, row 139 columns 88–90, row 139 columns
91–93, row 139 columns 94–359, row 140 columns 0–24), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4320 : rowsJ2 139 140 73 74 ≤ 6436307190287 := by decide +kernel

theorem rows22250R_4321 : rowsJ2 139 140 74 75 ≤ 5749817718830 := by decide +kernel

theorem rows22250R_4322 : rowsJ2 139 140 75 76 ≤ 5098738050732 := by decide +kernel

theorem rows22250R_4323 : rowsJ2 139 140 76 77 ≤ 4500115939614 := by decide +kernel

theorem rows22250R_4324 : rowsJ2 139 140 77 78 ≤ 3934534699960 := by decide +kernel

theorem rows22250R_4325 : rowsJ2 139 140 78 79 ≤ 3419379105797 := by decide +kernel

theorem rows22250R_4326 : rowsJ2 139 140 79 80 ≤ 2935119277178 := by decide +kernel

theorem rows22250R_4327 : rowsJ2 139 140 80 81 ≤ 2499478771855 := by decide +kernel

theorem rows22250R_4328 : rowsJ2 139 140 81 83 ≤ 3825918137654 := by decide +kernel

theorem rows22250R_4329 : rowsJ2 139 140 83 85 ≤ 2514456698945 := by decide +kernel

theorem rows22250R_4330 : rowsJ2 139 140 85 88 ≤ 2694173483009 := by decide +kernel

theorem rows22250R_4331 : rowsJ2 139 140 88 91 ≤ 8512854153876 := by decide +kernel

theorem rows22250R_4332 : rowsJ2 139 140 91 94 ≤ 18734861327015 := by decide +kernel

theorem rows22250R_4333 : rowsJ2 139 140 94 360 ≤ 549406111797519 := by decide +kernel

theorem rows22250R_4334 : rowsJ2 140 141 0 25 ≤ 3424850348004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4320
#print axioms SieveCert.rows22250R_4334
