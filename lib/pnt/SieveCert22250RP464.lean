/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5771–5784 of 5796

File 464 of 465: the parts `rows22250R_5771` … `rows22250R_5784` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94665 tests: rows 257–258, rows 259–260, rows 261–262, rows 263–264, rows
265–266, rows 267–268, rows 269–270, rows 271–272, rows 273–274, rows 275–276, rows 277–278, rows 279–280, rows
281–282, rows 283–284), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5771 : rows2 257 259 ≤ 18374527876308366 := by decide +kernel

theorem rows22250R_5772 : rows2 259 261 ≤ 18484757951962820 := by decide +kernel

theorem rows22250R_5773 : rows2 261 263 ≤ 18589302978264534 := by decide +kernel

theorem rows22250R_5774 : rows2 263 265 ≤ 18700973286910554 := by decide +kernel

theorem rows22250R_5775 : rows2 265 267 ≤ 18813277413109546 := by decide +kernel

theorem rows22250R_5776 : rows2 267 269 ≤ 18919482608544530 := by decide +kernel

theorem rows22250R_5777 : rows2 269 271 ≤ 19032390182400273 := by decide +kernel

theorem rows22250R_5778 : rows2 271 273 ≤ 19145431478637222 := by decide +kernel

theorem rows22250R_5779 : rows2 273 275 ≤ 19251778809387544 := by decide +kernel

theorem rows22250R_5780 : rows2 275 277 ≤ 19364210905141952 := by decide +kernel

theorem rows22250R_5781 : rows2 277 279 ≤ 19476053381434265 := by decide +kernel

theorem rows22250R_5782 : rows2 279 281 ≤ 19580351561586049 := by decide +kernel

theorem rows22250R_5783 : rows2 281 283 ≤ 19689838025440623 := by decide +kernel

theorem rows22250R_5784 : rows2 283 285 ≤ 19797692606227960 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5771
#print axioms SieveCert.rows22250R_5784
