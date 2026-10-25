/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3351–3366 of 5796

File 294 of 465: the parts `rows22250R_3351` … `rows22250R_3366` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98785 tests: row 110 columns 50–51, row 110 columns 52–54, row 110 columns
55–59, row 110 columns 60–68, row 110 columns 69–74, row 110 columns 75–78, row 110 columns 79–81, row 110 columns
82–83, row 110 columns 84–84, row 110 columns 85–85, row 110 columns 86–86, row 110 columns 87–87, row 110 columns
88–88, row 110 columns 89–89, row 110 columns 90–90, row 110 columns 91–91), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3351 : rowsJ2 110 111 50 52 ≤ 3377169769317 := by decide +kernel

theorem rows22250R_3352 : rowsJ2 110 111 52 55 ≤ 1900214416304 := by decide +kernel

theorem rows22250R_3353 : rowsJ2 110 111 55 60 ≤ 76552313406 := by decide +kernel

theorem rows22250R_3354 : rowsJ2 110 111 60 69 ≤ 0 := by decide +kernel

theorem rows22250R_3355 : rowsJ2 110 111 69 75 ≤ 0 := by decide +kernel

theorem rows22250R_3356 : rowsJ2 110 111 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_3357 : rowsJ2 110 111 79 82 ≤ 191998075614 := by decide +kernel

theorem rows22250R_3358 : rowsJ2 110 111 82 84 ≤ 796182592147 := by decide +kernel

theorem rows22250R_3359 : rowsJ2 110 111 84 85 ≤ 754190214563 := by decide +kernel

theorem rows22250R_3360 : rowsJ2 110 111 85 86 ≤ 1056033076762 := by decide +kernel

theorem rows22250R_3361 : rowsJ2 110 111 86 87 ≤ 958747475331 := by decide +kernel

theorem rows22250R_3362 : rowsJ2 110 111 87 88 ≤ 859325096103 := by decide +kernel

theorem rows22250R_3363 : rowsJ2 110 111 88 89 ≤ 804968403948 := by decide +kernel

theorem rows22250R_3364 : rowsJ2 110 111 89 90 ≤ 816958955436 := by decide +kernel

theorem rows22250R_3365 : rowsJ2 110 111 90 91 ≤ 874114706062 := by decide +kernel

theorem rows22250R_3366 : rowsJ2 110 111 91 92 ≤ 999519934543 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3351
#print axioms SieveCert.rows22250R_3366
