/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3726–3738 of 4715

File 286 of 351: the parts `rows22250R_3726` … `rows22250R_3738` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 90191 tests: row 139 columns 76–79, row 139 columns 80–339, row 140 columns
0–24, row 140 columns 25–48, row 140 columns 49–51, row 140 columns 52–53, row 140 columns 54–54, row 140 columns
55–55, row 140 columns 56–56, row 140 columns 57–57, row 140 columns 58–58, row 140 columns 59–59, row 140 columns
60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_3726 : rowsJ2 139 140 76 80 ≤ 3659455340863 := by decide +kernel

theorem rows22250R_3727 : rowsJ2 139 140 80 340 ≤ 863375942941100 := by decide +kernel

theorem rows22250R_3728 : rowsJ2 140 141 0 25 ≤ 3620538541711 := by decide +kernel

theorem rows22250R_3729 : rowsJ2 140 141 25 49 ≤ 4372132747098 := by decide +kernel

theorem rows22250R_3730 : rowsJ2 140 141 49 52 ≤ 8038271883425 := by decide +kernel

theorem rows22250R_3731 : rowsJ2 140 141 52 54 ≤ 8591472038166 := by decide +kernel

theorem rows22250R_3732 : rowsJ2 140 141 54 55 ≤ 5416338940449 := by decide +kernel

theorem rows22250R_3733 : rowsJ2 140 141 55 56 ≤ 6225462098272 := by decide +kernel

theorem rows22250R_3734 : rowsJ2 140 141 56 57 ≤ 7078778153685 := by decide +kernel

theorem rows22250R_3735 : rowsJ2 140 141 57 58 ≤ 7974582973786 := by decide +kernel

theorem rows22250R_3736 : rowsJ2 140 141 58 59 ≤ 8911308566675 := by decide +kernel

theorem rows22250R_3737 : rowsJ2 140 141 59 60 ≤ 9887516052097 := by decide +kernel

theorem rows22250R_3738 : rowsJ2 140 141 60 61 ≤ 10881246197582 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3726
#print axioms SieveCert.rows22250R_3738
