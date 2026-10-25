/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3516–3530 of 5796

File 304 of 465: the parts `rows22250R_3516` … `rows22250R_3530` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95990 tests: row 114 columns 38–38, row 114 columns 39–39, row 114 columns
40–40, row 114 columns 41–41, row 114 columns 42–43, row 114 columns 44–45, row 114 columns 46–47, row 114 columns
48–50, row 114 columns 51–55, row 114 columns 56–65, row 114 columns 66–72, row 114 columns 73–76, row 114 columns
77–79, row 114 columns 80–81, row 114 columns 82–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3516 : rowsJ2 114 115 38 39 ≤ 12723519526442 := by decide +kernel

theorem rows22250R_3517 : rowsJ2 114 115 39 40 ≤ 11653019708031 := by decide +kernel

theorem rows22250R_3518 : rowsJ2 114 115 40 41 ≤ 9998626062474 := by decide +kernel

theorem rows22250R_3519 : rowsJ2 114 115 41 42 ≤ 8513128404488 := by decide +kernel

theorem rows22250R_3520 : rowsJ2 114 115 42 44 ≤ 13226332743951 := by decide +kernel

theorem rows22250R_3521 : rowsJ2 114 115 44 46 ≤ 8878215801836 := by decide +kernel

theorem rows22250R_3522 : rowsJ2 114 115 46 48 ≤ 5109631569887 := by decide +kernel

theorem rows22250R_3523 : rowsJ2 114 115 48 51 ≤ 2749235084062 := by decide +kernel

theorem rows22250R_3524 : rowsJ2 114 115 51 56 ≤ 318309255717 := by decide +kernel

theorem rows22250R_3525 : rowsJ2 114 115 56 66 ≤ 391300971613 := by decide +kernel

theorem rows22250R_3526 : rowsJ2 114 115 66 73 ≤ 103118898854 := by decide +kernel

theorem rows22250R_3527 : rowsJ2 114 115 73 77 ≤ 0 := by decide +kernel

theorem rows22250R_3528 : rowsJ2 114 115 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_3529 : rowsJ2 114 115 80 82 ≤ 187309441949 := by decide +kernel

theorem rows22250R_3530 : rowsJ2 114 115 82 84 ≤ 772105320756 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3516
#print axioms SieveCert.rows22250R_3530
