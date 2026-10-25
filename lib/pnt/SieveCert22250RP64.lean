/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 595–604 of 5796

File 64 of 465: the parts `rows22250R_595` … `rows22250R_604` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 96914 tests: row 51 columns 44–44, row 51 columns 45–45, row 51 columns
46–46, row 51 columns 47–47, row 51 columns 48–48, row 51 columns 49–49, row 51 columns 50–50, row 51 columns
51–359, row 52 columns 0–14, row 52 columns 15–18), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_595 : rowsJ2 51 52 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_596 : rowsJ2 51 52 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_597 : rowsJ2 51 52 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_598 : rowsJ2 51 52 47 48 ≤ 122518023703 := by decide +kernel

theorem rows22250R_599 : rowsJ2 51 52 48 49 ≤ 549106050620 := by decide +kernel

theorem rows22250R_600 : rowsJ2 51 52 49 50 ≤ 1022507199638 := by decide +kernel

theorem rows22250R_601 : rowsJ2 51 52 50 51 ≤ 1537881054622 := by decide +kernel

theorem rows22250R_602 : rowsJ2 51 52 51 360 ≤ 2213774714823 := by decide +kernel

theorem rows22250R_603 : rowsJ2 52 53 0 15 ≤ 1897695236112 := by decide +kernel

theorem rows22250R_604 : rowsJ2 52 53 15 19 ≤ 1816407043302 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_595
#print axioms SieveCert.rows22250R_604
