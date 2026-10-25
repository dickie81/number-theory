/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 353–356 of 5796

File 31 of 465: the parts `rows22250R_353` … `rows22250R_356` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (4 parts, 85604 tests: row 42 columns 37–37, row 42 columns 38–38, row 42 columns
39–39, row 42 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_353 : rowsJ2 42 43 37 38 ≤ 337041772056 := by decide +kernel

theorem rows22250R_354 : rowsJ2 42 43 38 39 ≤ 307564511231 := by decide +kernel

theorem rows22250R_355 : rowsJ2 42 43 39 40 ≤ 267966230753 := by decide +kernel

theorem rows22250R_356 : rowsJ2 42 43 40 41 ≤ 235674243023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_353
#print axioms SieveCert.rows22250R_356
