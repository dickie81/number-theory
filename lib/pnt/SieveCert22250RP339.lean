/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4512–4528 of 4715

File 339 of 351: the parts `rows22250R_4512` … `rows22250R_4528` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97780 in units of a depth-4 test: row 178 columns 0–34, row 178 columns
35–36, row 178 columns 37–38, row 178 columns 39–39, row 178 columns 40–40, row 178 columns 41–41, row 178 columns
42–42, row 178 columns 43–43, row 178 columns 44–44, row 178 columns 45–45, row 178 columns 46–46, row 178 columns
47–47, row 178 columns 48–106, row 178 columns 107–339, row 179 columns 0–33, row 179 columns 34–36, row 179 columns
37–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_4512 : rowsJ2 178 179 0 35 ≤ 22186811125187 := by decide +kernel

theorem rows22250R_4513 : rowsJ2 178 179 35 37 ≤ 22934841545655 := by decide +kernel

theorem rows22250R_4514 : rowsJ2 178 179 37 39 ≤ 30834418091686 := by decide +kernel

theorem rows22250R_4515 : rowsJ2 178 179 39 40 ≤ 18188482094795 := by decide +kernel

theorem rows22250R_4516 : rowsJ2 178 179 40 41 ≤ 20136320415959 := by decide +kernel

theorem rows22250R_4517 : rowsJ2 178 179 41 42 ≤ 22156485437691 := by decide +kernel

theorem rows22250R_4518 : rowsJ2 178 179 42 43 ≤ 24247051485702 := by decide +kernel

theorem rows22250R_4519 : rowsJ2 178 179 43 44 ≤ 26406415650223 := by decide +kernel

theorem rows22250R_4520 : rowsJ2 178 179 44 45 ≤ 23714337440442 := by decide +kernel

theorem rows22250R_4521 : rowsJ2 178 179 45 46 ≤ 21193496469259 := by decide +kernel

theorem rows22250R_4522 : rowsJ2 178 179 46 47 ≤ 18837651868179 := by decide +kernel

theorem rows22250R_4523 : rowsJ2 178 179 47 48 ≤ 16641055365880 := by decide +kernel

theorem rows22250R_4524 : rowsJ2 178 179 48 107 ≤ 1076403071599144 := by decide +kernel

theorem rows22250R_4525 : rowsJ2 178 179 107 340 ≤ 1852973153512813 := by decide +kernel

theorem rows22250R_4526 : rowsJ2 179 180 0 34 ≤ 16992217397855 := by decide +kernel

theorem rows22250R_4527 : rowsJ2 179 180 34 37 ≤ 33734556732030 := by decide +kernel

theorem rows22250R_4528 : rowsJ2 179 180 37 39 ≤ 33425057194608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4512
#print axioms SieveCert.rows22250R_4528
