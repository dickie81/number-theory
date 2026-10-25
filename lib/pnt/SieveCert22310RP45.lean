/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 181–184 of 1732

File 45 of 430: the parts `rows22310R_181` … `rows22310R_184` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 72 columns 0–34, row 72 columns 35–43, row 72 columns 44–49,
row 72 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_181 : rowsJ2 72 73 0 35 ≤ 912744897332587 := by decide +kernel

theorem rows22310R_182 : rowsJ2 72 73 35 44 ≤ 198767376072616 := by decide +kernel

theorem rows22310R_183 : rowsJ2 72 73 44 50 ≤ 96303637602087 := by decide +kernel

theorem rows22310R_184 : rowsJ2 72 73 50 55 ≤ 104949004895392 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_181
#print axioms SieveCert.rows22310R_184
