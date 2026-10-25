/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5663–5678 of 5796

File 457 of 465: the parts `rows22250R_5663` … `rows22250R_5678` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97041 tests: row 196 columns 36–37, row 196 columns 38–38, row 196 columns
39–39, row 196 columns 40–40, row 196 columns 41–41, row 196 columns 42–42, row 196 columns 43–43, row 196 columns
44–359, row 197 columns 0–32, row 197 columns 33–35, row 197 columns 36–37, row 197 columns 38–38, row 197 columns
39–39, row 197 columns 40–40, row 197 columns 41–41, row 197 columns 42–42), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5663 : rowsJ2 196 197 36 38 ≤ 28471297285112 := by decide +kernel

theorem rows22250R_5664 : rowsJ2 196 197 38 39 ≤ 18745843525725 := by decide +kernel

theorem rows22250R_5665 : rowsJ2 196 197 39 40 ≤ 22186001373414 := by decide +kernel

theorem rows22250R_5666 : rowsJ2 196 197 40 41 ≤ 24217708618788 := by decide +kernel

theorem rows22250R_5667 : rowsJ2 196 197 41 42 ≤ 26314550569598 := by decide +kernel

theorem rows22250R_5668 : rowsJ2 196 197 42 43 ≤ 28475421448917 := by decide +kernel

theorem rows22250R_5669 : rowsJ2 196 197 43 44 ≤ 25747418954664 := by decide +kernel

theorem rows22250R_5670 : rowsJ2 196 197 44 360 ≤ 3644721057834754 := by decide +kernel

theorem rows22250R_5671 : rowsJ2 197 198 0 33 ≤ 12702149305173 := by decide +kernel

theorem rows22250R_5672 : rowsJ2 197 198 33 36 ≤ 26976466273471 := by decide +kernel

theorem rows22250R_5673 : rowsJ2 197 198 36 38 ≤ 30790112553323 := by decide +kernel

theorem rows22250R_5674 : rowsJ2 197 198 38 39 ≤ 20138893540448 := by decide +kernel

theorem rows22250R_5675 : rowsJ2 197 198 39 40 ≤ 23699872409174 := by decide +kernel

theorem rows22250R_5676 : rowsJ2 197 198 40 41 ≤ 25809955364090 := by decide +kernel

theorem rows22250R_5677 : rowsJ2 197 198 41 42 ≤ 27986008432529 := by decide +kernel

theorem rows22250R_5678 : rowsJ2 197 198 42 43 ≤ 27681145779358 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5663
#print axioms SieveCert.rows22250R_5678
