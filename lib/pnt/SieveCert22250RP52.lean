/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 501–505 of 5796

File 52 of 465: the parts `rows22250R_501` … `rows22250R_505` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 84851 tests: row 48 columns 37–37, row 48 columns 38–38, row 48 columns
39–39, row 48 columns 40–40, row 48 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_501 : rowsJ2 48 49 37 38 ≤ 72719484006 := by decide +kernel

theorem rows22250R_502 : rowsJ2 48 49 38 39 ≤ 59161391266 := by decide +kernel

theorem rows22250R_503 : rowsJ2 48 49 39 40 ≤ 44126301056 := by decide +kernel

theorem rows22250R_504 : rowsJ2 48 49 40 41 ≤ 34099367822 := by decide +kernel

theorem rows22250R_505 : rowsJ2 48 49 41 42 ≤ 23070752204 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_501
#print axioms SieveCert.rows22250R_505
