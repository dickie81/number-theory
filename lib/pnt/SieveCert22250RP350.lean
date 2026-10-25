/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4217–4228 of 5796

File 350 of 465: the parts `rows22250R_4217` … `rows22250R_4228` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 97011 tests: row 136 columns 67–67, row 136 columns 68–68, row 136 columns
69–69, row 136 columns 70–70, row 136 columns 71–71, row 136 columns 72–72, row 136 columns 73–73, row 136 columns
74–74, row 136 columns 75–75, row 136 columns 76–76, row 136 columns 77–77, row 136 columns 78–78), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4217 : rowsJ2 136 137 67 68 ≤ 5778645513694 := by decide +kernel

theorem rows22250R_4218 : rowsJ2 136 137 68 69 ≤ 6122787125489 := by decide +kernel

theorem rows22250R_4219 : rowsJ2 136 137 69 70 ≤ 6409370377081 := by decide +kernel

theorem rows22250R_4220 : rowsJ2 136 137 70 71 ≤ 6655644966678 := by decide +kernel

theorem rows22250R_4221 : rowsJ2 136 137 71 72 ≤ 6842853687786 := by decide +kernel

theorem rows22250R_4222 : rowsJ2 136 137 72 73 ≤ 6988218400254 := by decide +kernel

theorem rows22250R_4223 : rowsJ2 136 137 73 74 ≤ 6248885043317 := by decide +kernel

theorem rows22250R_4224 : rowsJ2 136 137 74 75 ≤ 5564365933949 := by decide +kernel

theorem rows22250R_4225 : rowsJ2 136 137 75 76 ≤ 4915039598014 := by decide +kernel

theorem rows22250R_4226 : rowsJ2 136 137 76 77 ≤ 4318245270025 := by decide +kernel

theorem rows22250R_4227 : rowsJ2 136 137 77 78 ≤ 3754267903160 := by decide +kernel

theorem rows22250R_4228 : rowsJ2 136 137 78 79 ≤ 3240787094113 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4217
#print axioms SieveCert.rows22250R_4228
