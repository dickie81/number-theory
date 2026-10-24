/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 536–539 of 561

File 136 of 142: the parts `rows22325R_536` … `rows22325R_539` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28522 tests: rows 171–173, rows 174–176, rows 177–179, rows 180–183), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_536 : rows2 171 174 ≤ 16532272833509363 := by decide +kernel

theorem rows22325R_537 : rows2 174 177 ≤ 17864450528980890 := by decide +kernel

theorem rows22325R_538 : rows2 177 180 ≤ 19227827642018086 := by decide +kernel

theorem rows22325R_539 : rows2 180 184 ≤ 27825133040397952 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_536
#print axioms SieveCert.rows22325R_539
