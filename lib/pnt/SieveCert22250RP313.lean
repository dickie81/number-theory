/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3656–3669 of 5796

File 313 of 465: the parts `rows22250R_3656` … `rows22250R_3669` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96177 tests: row 118 columns 38–39, row 118 columns 40–41, row 118 columns
42–43, row 118 columns 44–46, row 118 columns 47–51, row 118 columns 52–62, row 118 columns 63–67, row 118 columns
68–71, row 118 columns 72–75, row 118 columns 76–78, row 118 columns 79–80, row 118 columns 81–82, row 118 columns
83–85, row 118 columns 86–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3656 : rowsJ2 118 119 38 40 ≤ 17252975852579 := by decide +kernel

theorem rows22250R_3657 : rowsJ2 118 119 40 42 ≤ 12365268260052 := by decide +kernel

theorem rows22250R_3658 : rowsJ2 118 119 42 44 ≤ 8083127323969 := by decide +kernel

theorem rows22250R_3659 : rowsJ2 118 119 44 47 ≤ 6129161014135 := by decide +kernel

theorem rows22250R_3660 : rowsJ2 118 119 47 52 ≤ 1175641452590 := by decide +kernel

theorem rows22250R_3661 : rowsJ2 118 119 52 63 ≤ 300609085287 := by decide +kernel

theorem rows22250R_3662 : rowsJ2 118 119 63 68 ≤ 2570625998952 := by decide +kernel

theorem rows22250R_3663 : rowsJ2 118 119 68 72 ≤ 1160125211789 := by decide +kernel

theorem rows22250R_3664 : rowsJ2 118 119 72 76 ≤ 0 := by decide +kernel

theorem rows22250R_3665 : rowsJ2 118 119 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_3666 : rowsJ2 118 119 79 81 ≤ 45852082796 := by decide +kernel

theorem rows22250R_3667 : rowsJ2 118 119 81 83 ≤ 239466611478 := by decide +kernel

theorem rows22250R_3668 : rowsJ2 118 119 83 86 ≤ 139474240151 := by decide +kernel

theorem rows22250R_3669 : rowsJ2 118 119 86 89 ≤ 504126685308 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3656
#print axioms SieveCert.rows22250R_3669
