/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1228–1233 of 5796

File 127 of 465: the parts `rows22250R_1228` … `rows22250R_1233` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 91368 tests: row 67 columns 61–61, row 67 columns 62–62, row 67 columns
63–63, row 67 columns 64–64, row 67 columns 65–65, row 67 columns 66–66), each a sum of refined costs (`rows2` or
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

theorem rows22250R_1228 : rowsJ2 67 68 61 62 ≤ 10135549202029 := by decide +kernel

theorem rows22250R_1229 : rowsJ2 67 68 62 63 ≤ 10131140833521 := by decide +kernel

theorem rows22250R_1230 : rowsJ2 67 68 63 64 ≤ 9662536977226 := by decide +kernel

theorem rows22250R_1231 : rowsJ2 67 68 64 65 ≤ 9199042682043 := by decide +kernel

theorem rows22250R_1232 : rowsJ2 67 68 65 66 ≤ 8725257447986 := by decide +kernel

theorem rows22250R_1233 : rowsJ2 67 68 66 67 ≤ 8256262898084 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1228
#print axioms SieveCert.rows22250R_1233
