/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4295–4309 of 5796

File 356 of 465: the parts `rows22250R_4295` … `rows22250R_4309` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94476 tests: row 138 columns 81–82, row 138 columns 83–84, row 138 columns
85–87, row 138 columns 88–90, row 138 columns 91–93, row 138 columns 94–359, row 139 columns 0–24, row 139 columns
25–28, row 139 columns 29–37, row 139 columns 38–55, row 139 columns 56–57, row 139 columns 58–59, row 139 columns
60–60, row 139 columns 61–61, row 139 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4295 : rowsJ2 138 139 81 83 ≤ 3780483518936 := by decide +kernel

theorem rows22250R_4296 : rowsJ2 138 139 83 85 ≤ 2470382971482 := by decide +kernel

theorem rows22250R_4297 : rowsJ2 138 139 85 88 ≤ 2611961258827 := by decide +kernel

theorem rows22250R_4298 : rowsJ2 138 139 88 91 ≤ 8063259969633 := by decide +kernel

theorem rows22250R_4299 : rowsJ2 138 139 91 94 ≤ 17853428169744 := by decide +kernel

theorem rows22250R_4300 : rowsJ2 138 139 94 360 ≤ 630656647400077 := by decide +kernel

theorem rows22250R_4301 : rowsJ2 139 140 0 25 ≤ 2990120290630 := by decide +kernel

theorem rows22250R_4302 : rowsJ2 139 140 25 29 ≤ 9074147914336 := by decide +kernel

theorem rows22250R_4303 : rowsJ2 139 140 29 38 ≤ 3663460303284 := by decide +kernel

theorem rows22250R_4304 : rowsJ2 139 140 38 56 ≤ 3052914288272 := by decide +kernel

theorem rows22250R_4305 : rowsJ2 139 140 56 58 ≤ 3341353603757 := by decide +kernel

theorem rows22250R_4306 : rowsJ2 139 140 58 60 ≤ 5070756770351 := by decide +kernel

theorem rows22250R_4307 : rowsJ2 139 140 60 61 ≤ 3277957147499 := by decide +kernel

theorem rows22250R_4308 : rowsJ2 139 140 61 62 ≤ 3820118820613 := by decide +kernel

theorem rows22250R_4309 : rowsJ2 139 140 62 63 ≤ 4395879549175 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4295
#print axioms SieveCert.rows22250R_4309
