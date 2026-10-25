/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4501–4510 of 5796

File 372 of 465: the parts `rows22250R_4501` … `rows22250R_4510` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98729 tests: row 145 columns 60–60, row 145 columns 61–61, row 145 columns
62–62, row 145 columns 63–63, row 145 columns 64–64, row 145 columns 65–65, row 145 columns 66–66, row 145 columns
67–67, row 145 columns 68–68, row 145 columns 69–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4501 : rowsJ2 145 146 60 61 ≤ 5452257654187 := by decide +kernel

theorem rows22250R_4502 : rowsJ2 145 146 61 62 ≤ 6146837740999 := by decide +kernel

theorem rows22250R_4503 : rowsJ2 145 146 62 63 ≤ 6873780388103 := by decide +kernel

theorem rows22250R_4504 : rowsJ2 145 146 63 64 ≤ 7631968299639 := by decide +kernel

theorem rows22250R_4505 : rowsJ2 145 146 64 65 ≤ 8387232397046 := by decide +kernel

theorem rows22250R_4506 : rowsJ2 145 146 65 66 ≤ 9089438908220 := by decide +kernel

theorem rows22250R_4507 : rowsJ2 145 146 66 67 ≤ 9755242224708 := by decide +kernel

theorem rows22250R_4508 : rowsJ2 145 146 67 68 ≤ 10367633717205 := by decide +kernel

theorem rows22250R_4509 : rowsJ2 145 146 68 69 ≤ 10174927967488 := by decide +kernel

theorem rows22250R_4510 : rowsJ2 145 146 69 70 ≤ 9233566314480 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4501
#print axioms SieveCert.rows22250R_4510
