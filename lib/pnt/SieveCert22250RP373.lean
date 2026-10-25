/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4511–4524 of 5796

File 373 of 465: the parts `rows22250R_4511` … `rows22250R_4524` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96476 tests: row 145 columns 70–70, row 145 columns 71–71, row 145 columns
72–72, row 145 columns 73–73, row 145 columns 74–74, row 145 columns 75–75, row 145 columns 76–76, row 145 columns
77–77, row 145 columns 78–78, row 145 columns 79–80, row 145 columns 81–82, row 145 columns 83–86, row 145 columns
87–91, row 145 columns 92–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4511 : rowsJ2 145 146 70 71 ≤ 8352174481900 := by decide +kernel

theorem rows22250R_4512 : rowsJ2 145 146 71 72 ≤ 7512079346657 := by decide +kernel

theorem rows22250R_4513 : rowsJ2 145 146 72 73 ≤ 6729107767214 := by decide +kernel

theorem rows22250R_4514 : rowsJ2 145 146 73 74 ≤ 5984553718056 := by decide +kernel

theorem rows22250R_4515 : rowsJ2 145 146 74 75 ≤ 5294577619876 := by decide +kernel

theorem rows22250R_4516 : rowsJ2 145 146 75 76 ≤ 4640414738046 := by decide +kernel

theorem rows22250R_4517 : rowsJ2 145 146 76 77 ≤ 4038556646467 := by decide +kernel

theorem rows22250R_4518 : rowsJ2 145 146 77 78 ≤ 3470155724323 := by decide +kernel

theorem rows22250R_4519 : rowsJ2 145 146 78 79 ≤ 2952034317363 := by decide +kernel

theorem rows22250R_4520 : rowsJ2 145 146 79 81 ≤ 4492163690031 := by decide +kernel

theorem rows22250R_4521 : rowsJ2 145 146 81 83 ≤ 2873995471107 := by decide +kernel

theorem rows22250R_4522 : rowsJ2 145 146 83 87 ≤ 2325126083453 := by decide +kernel

theorem rows22250R_4523 : rowsJ2 145 146 87 92 ≤ 18619939619841 := by decide +kernel

theorem rows22250R_4524 : rowsJ2 145 146 92 360 ≤ 463246207711875 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4511
#print axioms SieveCert.rows22250R_4524
