/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 403–410 of 4715

File 39 of 351: the parts `rows22250R_403` … `rows22250R_410` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 99868 tests: row 45 columns 37–37, row 45 columns 38–38, row 45 columns
39–39, row 45 columns 40–40, row 45 columns 41–41, row 45 columns 42–42, row 45 columns 43–43, row 45 columns
44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_403 : rowsJ2 45 46 37 38 ≤ 63611860940 := by decide +kernel

theorem rows22250R_404 : rowsJ2 45 46 38 39 ≤ 47374274307 := by decide +kernel

theorem rows22250R_405 : rowsJ2 45 46 39 40 ≤ 33039310652 := by decide +kernel

theorem rows22250R_406 : rowsJ2 45 46 40 41 ≤ 23092937175 := by decide +kernel

theorem rows22250R_407 : rowsJ2 45 46 41 42 ≤ 15845360386 := by decide +kernel

theorem rows22250R_408 : rowsJ2 45 46 42 43 ≤ 13024881941 := by decide +kernel

theorem rows22250R_409 : rowsJ2 45 46 43 44 ≤ 10147098803 := by decide +kernel

theorem rows22250R_410 : rowsJ2 45 46 44 45 ≤ 87467467677 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_403
#print axioms SieveCert.rows22250R_410
