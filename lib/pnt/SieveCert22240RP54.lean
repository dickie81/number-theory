/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 534–540 of 5066

File 54 of 387: the parts `rows22240R_534` … `rows22240R_540` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 93154 in units of a depth-4 test: row 49 columns 36–36, row 49 columns
37–37, row 49 columns 38–38, row 49 columns 39–39, row 49 columns 40–40, row 49 columns 41–41, row 49 columns
42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_534 : rowsJ2 49 50 36 37 ≤ 64308619645 := by decide +kernel

theorem rows22240R_535 : rowsJ2 49 50 37 38 ≤ 48917432763 := by decide +kernel

theorem rows22240R_536 : rowsJ2 49 50 38 39 ≤ 33620846538 := by decide +kernel

theorem rows22240R_537 : rowsJ2 49 50 39 40 ≤ 23286345831 := by decide +kernel

theorem rows22240R_538 : rowsJ2 49 50 40 41 ≤ 13002229319 := by decide +kernel

theorem rows22240R_539 : rowsJ2 49 50 41 42 ≤ 8397073759 := by decide +kernel

theorem rows22240R_540 : rowsJ2 49 50 42 43 ≤ 3806036018 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_534
#print axioms SieveCert.rows22240R_540
