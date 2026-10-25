/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2704–2719 of 4715

File 218 of 351: the parts `rows22250R_2704` … `rows22250R_2719` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99266 tests: row 102 columns 43–44, row 102 columns 45–46, row 102 columns
47–48, row 102 columns 49–51, row 102 columns 52–56, row 102 columns 57–65, row 102 columns 66–71, row 102 columns
72–75, row 102 columns 76–78, row 102 columns 79–79, row 102 columns 80–80, row 102 columns 81–81, row 102 columns
82–82, row 102 columns 83–83, row 102 columns 84–84, row 102 columns 85–85), each a sum of refined costs (`rows2` or
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

theorem rows22250R_2704 : rowsJ2 102 103 43 45 ≤ 14782803356187 := by decide +kernel

theorem rows22250R_2705 : rowsJ2 102 103 45 47 ≤ 9667345580982 := by decide +kernel

theorem rows22250R_2706 : rowsJ2 102 103 47 49 ≤ 5334700048581 := by decide +kernel

theorem rows22250R_2707 : rowsJ2 102 103 49 52 ≤ 2959424921032 := by decide +kernel

theorem rows22250R_2708 : rowsJ2 102 103 52 57 ≤ 376943397465 := by decide +kernel

theorem rows22250R_2709 : rowsJ2 102 103 57 66 ≤ 0 := by decide +kernel

theorem rows22250R_2710 : rowsJ2 102 103 66 72 ≤ 0 := by decide +kernel

theorem rows22250R_2711 : rowsJ2 102 103 72 76 ≤ 15330987044 := by decide +kernel

theorem rows22250R_2712 : rowsJ2 102 103 76 79 ≤ 787850276267 := by decide +kernel

theorem rows22250R_2713 : rowsJ2 102 103 79 80 ≤ 736644834157 := by decide +kernel

theorem rows22250R_2714 : rowsJ2 102 103 80 81 ≤ 1075756043515 := by decide +kernel

theorem rows22250R_2715 : rowsJ2 102 103 81 82 ≤ 1487867320460 := by decide +kernel

theorem rows22250R_2716 : rowsJ2 102 103 82 83 ≤ 1350173486934 := by decide +kernel

theorem rows22250R_2717 : rowsJ2 102 103 83 84 ≤ 1226892513031 := by decide +kernel

theorem rows22250R_2718 : rowsJ2 102 103 84 85 ≤ 1100688552596 := by decide +kernel

theorem rows22250R_2719 : rowsJ2 102 103 85 86 ≤ 1070838664976 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2704
#print axioms SieveCert.rows22250R_2719
