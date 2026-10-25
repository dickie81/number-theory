/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4256–4270 of 5796

File 353 of 465: the parts `rows22250R_4256` … `rows22250R_4270` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98391 tests: row 137 columns 74–74, row 137 columns 75–75, row 137 columns
76–76, row 137 columns 77–77, row 137 columns 78–78, row 137 columns 79–79, row 137 columns 80–80, row 137 columns
81–82, row 137 columns 83–84, row 137 columns 85–87, row 137 columns 88–90, row 137 columns 91–93, row 137 columns
94–359, row 138 columns 0–24, row 138 columns 25–28), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4256 : rowsJ2 137 138 74 75 ≤ 5654129363509 := by decide +kernel

theorem rows22250R_4257 : rowsJ2 137 138 75 76 ≤ 5004223049704 := by decide +kernel

theorem rows22250R_4258 : rowsJ2 137 138 76 77 ≤ 4406823647375 := by decide +kernel

theorem rows22250R_4259 : rowsJ2 137 138 77 78 ≤ 3842316638925 := by decide +kernel

theorem rows22250R_4260 : rowsJ2 137 138 78 79 ≤ 3328282302600 := by decide +kernel

theorem rows22250R_4261 : rowsJ2 137 138 79 80 ≤ 2844990365069 := by decide +kernel

theorem rows22250R_4262 : rowsJ2 137 138 80 81 ≤ 2410362210469 := by decide +kernel

theorem rows22250R_4263 : rowsJ2 137 138 81 83 ≤ 3650287738135 := by decide +kernel

theorem rows22250R_4264 : rowsJ2 137 138 83 85 ≤ 2341952920200 := by decide +kernel

theorem rows22250R_4265 : rowsJ2 137 138 85 88 ≤ 2357737111271 := by decide +kernel

theorem rows22250R_4266 : rowsJ2 137 138 88 91 ≤ 7459377583366 := by decide +kernel

theorem rows22250R_4267 : rowsJ2 137 138 91 94 ≤ 16934878007464 := by decide +kernel

theorem rows22250R_4268 : rowsJ2 137 138 94 360 ≤ 640396685548485 := by decide +kernel

theorem rows22250R_4269 : rowsJ2 138 139 0 25 ≤ 2552563293056 := by decide +kernel

theorem rows22250R_4270 : rowsJ2 138 139 25 29 ≤ 10588639318884 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4256
#print axioms SieveCert.rows22250R_4270
