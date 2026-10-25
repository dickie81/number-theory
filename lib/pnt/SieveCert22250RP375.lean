/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4538–4546 of 5796

File 375 of 465: the parts `rows22250R_4538` … `rows22250R_4546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93718 tests: row 146 columns 65–65, row 146 columns 66–66, row 146 columns
67–67, row 146 columns 68–68, row 146 columns 69–69, row 146 columns 70–70, row 146 columns 71–71, row 146 columns
72–72, row 146 columns 73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4538 : rowsJ2 146 147 65 66 ≤ 9657334027500 := by decide +kernel

theorem rows22250R_4539 : rowsJ2 146 147 66 67 ≤ 10349997363383 := by decide +kernel

theorem rows22250R_4540 : rowsJ2 146 147 67 68 ≤ 10989642604777 := by decide +kernel

theorem rows22250R_4541 : rowsJ2 146 147 68 69 ≤ 10003104955435 := by decide +kernel

theorem rows22250R_4542 : rowsJ2 146 147 69 70 ≤ 9061107881941 := by decide +kernel

theorem rows22250R_4543 : rowsJ2 146 147 70 71 ≤ 8179053212573 := by decide +kernel

theorem rows22250R_4544 : rowsJ2 146 147 71 72 ≤ 7338355973519 := by decide +kernel

theorem rows22250R_4545 : rowsJ2 146 147 72 73 ≤ 6554755408808 := by decide +kernel

theorem rows22250R_4546 : rowsJ2 146 147 73 74 ≤ 5809634666579 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4538
#print axioms SieveCert.rows22250R_4546
