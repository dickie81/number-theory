/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3987–4002 of 4715

File 305 of 351: the parts `rows22250R_3987` … `rows22250R_4002` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97930 tests: row 150 columns 58–58, row 150 columns 59–59, row 150 columns
60–60, row 150 columns 61–61, row 150 columns 62–62, row 150 columns 63–63, row 150 columns 64–64, row 150 columns
65–65, row 150 columns 66–67, row 150 columns 68–70, row 150 columns 71–76, row 150 columns 77–339, row 151 columns
0–42, row 151 columns 43–45, row 151 columns 46–47, row 151 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3987 : rowsJ2 150 151 58 59 ≤ 13809713458205 := by decide +kernel

theorem rows22250R_3988 : rowsJ2 150 151 59 60 ≤ 12361105002681 := by decide +kernel

theorem rows22250R_3989 : rowsJ2 150 151 60 61 ≤ 11002954201403 := by decide +kernel

theorem rows22250R_3990 : rowsJ2 150 151 61 62 ≤ 9732829262049 := by decide +kernel

theorem rows22250R_3991 : rowsJ2 150 151 62 63 ≤ 8548473140170 := by decide +kernel

theorem rows22250R_3992 : rowsJ2 150 151 63 64 ≤ 7447795511133 := by decide +kernel

theorem rows22250R_3993 : rowsJ2 150 151 64 65 ≤ 6428865484605 := by decide +kernel

theorem rows22250R_3994 : rowsJ2 150 151 65 66 ≤ 5489905011549 := by decide +kernel

theorem rows22250R_3995 : rowsJ2 150 151 66 68 ≤ 8474792617925 := by decide +kernel

theorem rows22250R_3996 : rowsJ2 150 151 68 71 ≤ 7582877571074 := by decide +kernel

theorem rows22250R_3997 : rowsJ2 150 151 71 77 ≤ 3869317619358 := by decide +kernel

theorem rows22250R_3998 : rowsJ2 150 151 77 340 ≤ 2003608937163831 := by decide +kernel

theorem rows22250R_3999 : rowsJ2 151 152 0 43 ≤ 4336399867246 := by decide +kernel

theorem rows22250R_4000 : rowsJ2 151 152 43 46 ≤ 8710958152445 := by decide +kernel

theorem rows22250R_4001 : rowsJ2 151 152 46 48 ≤ 9531799021168 := by decide +kernel

theorem rows22250R_4002 : rowsJ2 151 152 48 49 ≤ 6065723891314 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3987
#print axioms SieveCert.rows22250R_4002
