/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 615–620 of 5796

File 66 of 465: the parts `rows22250R_615` … `rows22250R_620` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 90383 tests: row 52 columns 33–33, row 52 columns 34–34, row 52 columns
35–35, row 52 columns 36–36, row 52 columns 37–37, row 52 columns 38–38), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_615 : rowsJ2 52 53 33 34 ≤ 51115381940 := by decide +kernel

theorem rows22250R_616 : rowsJ2 52 53 34 35 ≤ 39927537367 := by decide +kernel

theorem rows22250R_617 : rowsJ2 52 53 35 36 ≤ 27868197781 := by decide +kernel

theorem rows22250R_618 : rowsJ2 52 53 36 37 ≤ 19799408112 := by decide +kernel

theorem rows22250R_619 : rowsJ2 52 53 37 38 ≤ 11289065150 := by decide +kernel

theorem rows22250R_620 : rowsJ2 52 53 38 39 ≤ 6791216864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_615
#print axioms SieveCert.rows22250R_620
