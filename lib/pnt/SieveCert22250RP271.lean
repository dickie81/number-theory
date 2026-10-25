/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3001–3016 of 5796

File 271 of 465: the parts `rows22250R_3001` … `rows22250R_3016` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 93997 tests: row 103 columns 48–48, row 103 columns 49–49, row 103 columns
50–50, row 103 columns 51–51, row 103 columns 52–52, row 103 columns 53–54, row 103 columns 55–56, row 103 columns
57–58, row 103 columns 59–61, row 103 columns 62–66, row 103 columns 67–72, row 103 columns 73–77, row 103 columns
78–80, row 103 columns 81–82, row 103 columns 83–83, row 103 columns 84–84), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3001 : rowsJ2 103 104 48 49 ≤ 7746319727038 := by decide +kernel

theorem rows22250R_3002 : rowsJ2 103 104 49 50 ≤ 6536503213216 := by decide +kernel

theorem rows22250R_3003 : rowsJ2 103 104 50 51 ≤ 5466725977012 := by decide +kernel

theorem rows22250R_3004 : rowsJ2 103 104 51 52 ≤ 4534503674159 := by decide +kernel

theorem rows22250R_3005 : rowsJ2 103 104 52 53 ≤ 3663821924358 := by decide +kernel

theorem rows22250R_3006 : rowsJ2 103 104 53 55 ≤ 4964203259715 := by decide +kernel

theorem rows22250R_3007 : rowsJ2 103 104 55 57 ≤ 2308188728384 := by decide +kernel

theorem rows22250R_3008 : rowsJ2 103 104 57 59 ≤ 475259653702 := by decide +kernel

theorem rows22250R_3009 : rowsJ2 103 104 59 62 ≤ 0 := by decide +kernel

theorem rows22250R_3010 : rowsJ2 103 104 62 67 ≤ 0 := by decide +kernel

theorem rows22250R_3011 : rowsJ2 103 104 67 73 ≤ 0 := by decide +kernel

theorem rows22250R_3012 : rowsJ2 103 104 73 78 ≤ 0 := by decide +kernel

theorem rows22250R_3013 : rowsJ2 103 104 78 81 ≤ 50353305955 := by decide +kernel

theorem rows22250R_3014 : rowsJ2 103 104 81 83 ≤ 462933317738 := by decide +kernel

theorem rows22250R_3015 : rowsJ2 103 104 83 84 ≤ 523309542161 := by decide +kernel

theorem rows22250R_3016 : rowsJ2 103 104 84 85 ≤ 794413748530 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3001
#print axioms SieveCert.rows22250R_3016
